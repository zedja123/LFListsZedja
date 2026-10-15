#!/usr/bin/env python3
"""Reference implementation of the Domain banlist extension.

This file is the executable definition that the client (MASQPro
gframe/deck_manager.cpp) and the server (Multirole BanlistParser.hpp and
Room/Context.cpp) are checked against. It implements:

  (a) parsing a .lflist.conf file, including the Domain extension;
  (b) the list hash, computed exactly as the client computes it for ordinary
      lists and Genesys lists, plus the Domain contributions;
  (c) the Domain deck check (Deck Master, sizes, singleton, domain membership).

Python 3 standard library only. Usage:

  domain_ref.py hash <file.lflist.conf>...
  domain_ref.py selftest | vectors <out.conf>
  domain_ref.py show <file.lflist.conf> <code>
  domain_ref.py check --babel <BabelCDB dir> [--list <file>] <deck.ydk>...
  domain_ref.py count --babel <BabelCDB dir> [--list <file>] <code>...

File format
-----------
Every line is read as bytes. As in the client, everything from the first
carriage return on is dropped, and empty lines are skipped. Then:

  "#@..."      inside a Domain list (after its "$domain" line): a Domain data
               line, see below. Anywhere else: a comment.
  "#..."       comment.
  "!<name>"    starts a new list.
  "$whitelist" (prefix) the current list is a whitelist.
  "$genesys"   (prefix) Genesys list; ignored outside a list, after a
               "$genesys" and after a "$domain" line.
  "$domain"    (prefix) Domain list; ignored outside a list, after a
               "$domain" and after a "$genesys" line.
  "<code> <count>[ <points>]..."  ordinary card line (inside a list only).

Domain data lines (fields are separated by spaces or tabs):

  #@forbid-dm <code>
  #@dm <code> [a=<hex>] [r=<hex>] [s=<hex>,<hex>...] [n=<code>,<code>...]

  <code> and n entries are decimal, 1 to 4294967295. a (attribute mask, 32 bits),
  r (race mask, 64 bits) and s entries (16-bit archetype codes) are hexadecimal
  without a "0x" prefix. Any field may be omitted or empty ("s="). Empty list
  items (a stray comma) and zero s entries are ignored. Unknown keys are
  ignored. A later field with the same key replaces the earlier one. A line
  whose code or any value does not parse, or with an unknown directive, is
  skipped; it is still hashed. For a code that has several lines, the first
  one wins (also for the hash: every line is hashed).

Hash
----
  hash = 0x7DFCEE6A at "!<name>"
  ordinary card line:   hash ^= rotl(code, 18) ^ rotl'(code, count)
                        (exact C++ expression, see card_line_salt)
  Genesys:              hash ^= GenesysCapSalt(cap), GenesysPointsSalt(code, pts)
  "$domain":            hash ^= 0x444F4D41 (DomainSalt)
  every "#@" line of a Domain list:
                        hash ^= rotl32(fnv1a32(text), 1)
                        text = the bytes after "#@", with trailing spaces and
                        tabs removed (the carriage return is already gone).

Deck check (spec section 3 with amendments D2, D3, D10)
-------------------------------------------------------
See check_deck(). Membership of a Main/Extra card X in the domain of the Deck
Master is in_domain().
"""
import argparse
import glob
import os
import sqlite3
import sys

BANLIST_HASH_MAGIC = 0x7DFCEE6A
DOMAIN_SALT = 0x444F4D41
FNV_OFFSET = 0x811C9DC5
FNV_PRIME = 0x01000193
M32 = 0xFFFFFFFF
M64 = 0xFFFFFFFFFFFFFFFF

TYPE_MONSTER = 0x1
TYPE_SPELL = 0x2
TYPE_TRAP = 0x4
TYPE_FUSION = 0x40
TYPE_RITUAL = 0x80
TYPE_TOKEN = 0x4000
TYPE_SYNCHRO = 0x2000
TYPE_XYZ = 0x800000
TYPE_LINK = 0x4000000
TYPE_SKILL = 0x8000000
TYPES_EXTRA = TYPE_FUSION | TYPE_SYNCHRO | TYPE_XYZ | TYPE_LINK
ATTRIBUTE_DIVINE = 0x40
RACE_DIVINE = 0x200000
SCOPE_OCG = 0x1
SCOPE_TCG = 0x2
SCOPE_CUSTOM = 0x20
SCOPE_PRERELEASE = 0x100
SCOPE_RUSH = 0x200
SCOPE_LEGEND = 0x400

# DeckError types (client network.h, Multirole DeckOrCard).
LFLIST = 0x1
OCGONLY = 0x2
TCGONLY = 0x3
UNKNOWNCARD = 0x4
MAINCOUNT = 0x6
EXTRACOUNT = 0x7
SIDECOUNT = 0x8
FORBTYPE = 0x9
UNOFFICIALCARD = 0xA
DOMAIN_DECK_MASTER = 0x11
DOMAIN_OUT_OF_DOMAIN = 0x12
DOMAIN_SINGLETON = 0x13
DOMAIN_FORBIDDEN_DM = 0x14
ERROR_NAMES = {
	LFLIST: 'LFLIST', OCGONLY: 'OCGONLY', TCGONLY: 'TCGONLY', UNKNOWNCARD: 'UNKNOWNCARD',
	MAINCOUNT: 'MAINCOUNT', EXTRACOUNT: 'EXTRACOUNT', SIDECOUNT: 'SIDECOUNT', FORBTYPE: 'FORBTYPE',
	UNOFFICIALCARD: 'UNOFFICIALCARD', DOMAIN_DECK_MASTER: 'DOMAIN_DECK_MASTER',
	DOMAIN_OUT_OF_DOMAIN: 'DOMAIN_OUT_OF_DOMAIN', DOMAIN_SINGLETON: 'DOMAIN_SINGLETON',
	DOMAIN_FORBIDDEN_DM: 'DOMAIN_FORBIDDEN_DM',
}

# Domain deck sizes (rule index 9): Main 60-60, Extra 0-15, Side 0-0.
DOMAIN_SIZES = dict(main=(60, 60), extra=(0, 15), side=(0, 0))


# ---------------------------------------------------------------------------
# Hash primitives
# ---------------------------------------------------------------------------

def rotl32(x, n):
	x &= M32
	return ((x << n) | (x >> (32 - n))) & M32


def fnv1a32(data):
	h = FNV_OFFSET
	for b in data:
		h = ((h ^ b) * FNV_PRIME) & M32
	return h


def domain_line_salt(text):
	"""Contribution of one "#@" line; text is the bytes after "#@", trimmed."""
	return rotl32(fnv1a32(text), 1)


def card_line_salt(code, count):
	"""((code << 18) | (code >> 14)) ^ ((code << (27 + count)) | (code >> (5 - count)))
	on uint32_t code and int32_t count. Shift amounts are reduced modulo 32 as on
	x86; in C++ a count outside -27..4 is undefined behaviour anyway."""
	code &= M32
	s1 = (27 + count) & 31
	s2 = (5 - count) & 31
	return (((code << 18) | (code >> 14)) ^ ((code << s1) | (code >> s2))) & M32


def genesys_cap_salt(cap):
	return (0x47454E53 ^ (cap * 0x9E3779B1)) & M32


def genesys_points_salt(code, points):
	return (((code << 7) | (code >> 25)) ^ (points * 0x85EBCA77)) & M32


# ---------------------------------------------------------------------------
# C++ number parsing used by the client (std::stoul / std::stol, LP64)
# ---------------------------------------------------------------------------

_CSPACE = b' \t\n\v\f\r'


def _strto(s, signed):
	i = 0
	while i < len(s) and s[i] in _CSPACE:
		i += 1
	neg = False
	if i < len(s) and s[i] in b'+-':
		neg = s[i] == ord('-')
		i += 1
	j = i
	while j < len(s) and 0x30 <= s[j] <= 0x39:
		j += 1
	if j == i:
		raise ValueError('invalid_argument')
	v = int(s[i:j])
	if signed:
		v = -v if neg else v
		if not -(1 << 63) <= v < (1 << 63):
			raise OverflowError('out_of_range')
		return v
	if v > M64:
		raise OverflowError('out_of_range')
	return (-v) & M64 if neg else v


def stoul(s):
	return _strto(s, False)


def stol(s):
	return _strto(s, True)


def _find_first_not_of(s, chars, start=0):
	for i in range(start, len(s)):
		if s[i] not in chars:
			return i
	return -1


# ---------------------------------------------------------------------------
# (a) + (b) Parsing and hashing
# ---------------------------------------------------------------------------

class DomainEntry:
	__slots__ = ('code', 'attribute', 'race', 'setcodes', 'names')

	def __init__(self, code, attribute=0, race=0, setcodes=(), names=()):
		self.code = code
		self.attribute = attribute
		self.race = race
		self.setcodes = tuple(setcodes)
		self.names = frozenset(names)

	def __eq__(self, other):
		return (self.code, self.attribute, self.race, sorted(self.setcodes), self.names) == \
			(other.code, other.attribute, other.race, sorted(other.setcodes), other.names)

	def __repr__(self):
		return 'DomainEntry(%d, a=%x, r=%x, s=%s, n=%s)' % (
			self.code, self.attribute, self.race, ','.join('%x' % s for s in self.setcodes),
			','.join(str(n) for n in sorted(self.names)))


class LFList:
	def __init__(self, name):
		self.name = name
		self.hash = BANLIST_HASH_MAGIC
		self.content = {}
		self.whitelist = False
		self.genesys = False
		self.genesys_cap = 0
		self.points = {}
		self.domain = False
		self.dm = {}          # code -> DomainEntry (first line wins)
		self.forbid_dm = set()
		self.malformed = []   # "#@" lines that were hashed but not understood

	def limitation(self, card):
		"""LFList::GetLimitationIterator: own code, then the alias (whitelists only
		follow an alias within the artwork range)."""
		if card.code in self.content:
			return self.content[card.code]
		if card.alias and (not self.whitelist or card.in_artwork_range()):
			return self.content.get(card.alias)
		return None


_DIGITS = {10: frozenset(b'0123456789'), 16: frozenset(b'0123456789abcdefABCDEF')}


def _parse_uint(tok, base, limit):
	if not tok or any(c not in _DIGITS[base] for c in tok):
		raise ValueError(tok)
	v = int(tok, base)
	if v > limit:
		raise ValueError(tok)
	return v


def parse_domain_line(lst, text):
	"""Parse the bytes after "#@" (already trimmed) into lst. Returns False if the
	line is malformed or unknown (it is skipped)."""
	toks = text.replace(b'\t', b' ').split()
	if not toks:
		return False
	try:
		if toks[0] == b'forbid-dm':
			if len(toks) != 2:
				return False
			code = _parse_uint(toks[1], 10, M32)
			if code == 0:
				return False
			lst.forbid_dm.add(code)
			return True
		if toks[0] != b'dm' or len(toks) < 2:
			return False
		code = _parse_uint(toks[1], 10, M32)
		if code == 0:
			return False
		fields = {}
		for tok in toks[2:]:
			key, eq, val = tok.partition(b'=')
			if not eq:
				return False
			items = [x for x in val.split(b',') if x]
			if key == b'a':
				fields['a'] = _parse_uint(items[0], 16, M32) if items else 0
				if len(items) > 1:
					return False
			elif key == b'r':
				fields['r'] = _parse_uint(items[0], 16, M64) if items else 0
				if len(items) > 1:
					return False
			elif key == b's':
				fields['s'] = [v for v in (_parse_uint(x, 16, 0xFFFF) for x in items) if v]
			elif key == b'n':
				fields['n'] = [_parse_uint(x, 10, M32) for x in items]
		if code not in lst.dm:
			lst.dm[code] = DomainEntry(code, fields.get('a', 0), fields.get('r', 0),
				sorted(set(fields.get('s', ()))), fields.get('n', ()))
		return True
	except ValueError:
		return False


def parse_lflist_bytes(data):
	"""Parse a whole .lflist.conf file (bytes). Returns the lists in file order."""
	lists = []
	cur = None
	for raw in data.split(b'\n'):
		pos = raw.find(b'\r')
		line = raw if pos < 0 else raw[:pos]
		if not line:
			continue
		if line[0] == ord('#'):
			if cur is not None and cur.domain and line.startswith(b'#@'):
				text = line[2:].rstrip(b' \t')
				cur.hash ^= domain_line_salt(text)
				if not parse_domain_line(cur, text):
					cur.malformed.append(text)
			continue
		if line[0] == ord('!'):
			if cur is not None:
				lists.append(cur)
			cur = LFList(line[1:].decode('utf-8', 'replace'))
			continue
		if line.startswith(b'$whitelist'):
			if cur is not None:
				cur.whitelist = True
			continue
		if line.startswith(b'$genesys'):
			if cur is None or cur.genesys or cur.domain:
				continue
			cap = 100
			b = next((i for i in range(len(b'$genesys'), len(line)) if 0x30 <= line[i] <= 0x39), -1)
			if b >= 0:
				try:
					cap = stoul(line[b:]) & M32
				except (ValueError, OverflowError):
					pass
			cur.genesys = True
			cur.genesys_cap = cap
			cur.hash ^= genesys_cap_salt(cap)
			continue
		if line.startswith(b'$domain'):
			if cur is None or cur.domain or cur.genesys:
				continue
			cur.domain = True
			cur.hash ^= DOMAIN_SALT
			continue
		if cur is None:
			continue
		_parse_card_line(cur, line)
	if cur is not None:
		lists.append(cur)
	return lists


def _parse_card_line(cur, s):
	"""Ordinary card line, as DeckManager::LoadLFListSingle parses it."""
	p = s.find(b' ')
	if p < 0:
		return
	c = _find_first_not_of(s, b'-0123456789', p + 1)
	try:
		code = stoul(s[:p]) & M32
		if code == 0:
			return
		count_text = s[p:] if c < 0 else s[p:c]
		count = stol(count_text)
		count = ((count + (1 << 31)) & M32) - (1 << 31)  # static_cast<int32_t>
		cur.content[code] = count
		cur.hash ^= card_line_salt(code, count)
		if c >= 0:
			pb = _find_first_not_of(s, b' \t', c)
			if pb >= 0 and 0x30 <= s[pb] <= 0x39:
				points = stoul(s[pb:]) & M32
				if points > 0:
					cur.points[code] = points
					cur.hash ^= genesys_points_salt(code, points)
	except (ValueError, OverflowError):
		pass


def parse_lflist(path):
	with open(path, 'rb') as f:
		return parse_lflist_bytes(f.read())


def find_domain_list(path):
	for lst in parse_lflist(path):
		if lst.domain:
			return lst
	raise SystemExit('%s: no Domain list ("$domain") found' % path)


# ---------------------------------------------------------------------------
# Card data
# ---------------------------------------------------------------------------

class Card:
	__slots__ = ('code', 'ot', 'alias', 'setcode', 'type', 'level', 'race', 'attribute', 'name', 'desc')

	def __init__(self, row):
		(self.code, self.ot, self.alias, self.setcode, self.type, self.level, self.race,
		 self.attribute, self.name, self.desc) = row
		self.setcode &= M64
		self.race &= M64
		self.desc = self.desc or ''

	def setcodes(self):
		return [v for v in ((self.setcode >> (16 * k)) & 0xFFFF for k in range(4)) if v]

	def in_artwork_range(self):
		# Only used for the ordinary banlist lookup; Domain lookups use alias != 0 (D10).
		return self.alias != 0 and ((self.alias - self.code) & M32 < 10 or (self.code - self.alias) & M32 < 10)

	def canonical(self):
		return self.alias if self.alias else self.code


def babel_cdbs(babel_dir):
	"""The databases the Domain data is built from (amendment D4): cards.cdb,
	release-*.cdb and prerelease-*.cdb, never the Rush, Skill, unofficial or
	GOAT databases."""
	files = [os.path.join(babel_dir, 'cards.cdb')]
	files += sorted(glob.glob(os.path.join(babel_dir, 'release-*.cdb')))
	files += sorted(f for f in glob.glob(os.path.join(babel_dir, 'prerelease-*.cdb'))
		if 'rush' not in os.path.basename(f).lower())
	missing = [f for f in files if not os.path.isfile(f)]
	if missing:
		raise SystemExit('missing card database: %s' % ', '.join(missing))
	return files


def load_cards(files):
	"""Rows of all files; for a code present in several files the first file wins.
	Rush and Legend rows are left out."""
	cards = {}
	for path in files:
		con = sqlite3.connect('file:%s?mode=ro' % path, uri=True)
		try:
			q = ('select d.id, d.ot, d.alias, d.setcode, d.type, d.level, d.race, d.attribute, t.name, t.desc '
				'from datas d join texts t on d.id = t.id order by d.id')
			for row in con.execute(q):
				if row[0] in cards or row[1] & (SCOPE_RUSH | SCOPE_LEGEND):
					continue
				cards[row[0]] = Card(row)
		finally:
			con.close()
	return cards


# ---------------------------------------------------------------------------
# (c) Deck check
# ---------------------------------------------------------------------------

def match_setcode(d, x):
	"""Engine test card::match_setcode: domain archetype d, card setcode x."""
	return (d & 0xFFF) == (x & 0xFFF) and (d & x) == d


def card_archetypes(card, cards):
	"""Archetypes of X (D2): setcodes of X's own row and of its alias row."""
	out = set(card.setcodes())
	if card.alias and card.alias in cards:
		out.update(cards[card.alias].setcodes())
	return out


def lookup_dm(lst, dm):
	"""#@dm line of a Deck Master: its own code, then its alias (D1, D10)."""
	e = lst.dm.get(dm.code)
	if e is None and dm.alias:
		e = lst.dm.get(dm.alias)
	return e


def is_forbidden_dm(lst, dm):
	return dm.code in lst.forbid_dm or (dm.alias != 0 and dm.alias in lst.forbid_dm)


def deck_master_domain(lst, dm):
	"""The domain used for the check: the #@dm line (or the fallback: own attribute,
	race and setcodes as-is), always OR-ed with the Deck Master's own attribute,
	race and setcodes (D2)."""
	e = lookup_dm(lst, dm)
	attribute, race, sets, names = dm.attribute, dm.race, set(dm.setcodes()), frozenset()
	if e is not None:
		attribute |= e.attribute
		race |= e.race
		sets.update(e.setcodes)
		names = e.names
	return DomainEntry(dm.code, attribute, race, sorted(sets), names)


def in_domain(x, dom, cards):
	"""Membership of card X in a domain (D2). Returns the reason or None."""
	if x.type & (TYPE_SPELL | TYPE_TRAP):
		return 'spell/trap'
	if not x.type & TYPE_MONSTER:
		return None
	if x.attribute & ATTRIBUTE_DIVINE or x.race & RACE_DIVINE:
		return 'divine'
	if x.code in dom.names or (x.alias and x.alias in dom.names):
		return 'name'
	xs = card_archetypes(x, cards)
	if any(match_setcode(d, v) for d in dom.setcodes for v in xs):
		return 'archetype'
	if x.attribute & dom.attribute:
		return 'attribute'
	if x.race & dom.race:
		return 'race'
	return None


# Allowed-cards settings (DuelAllowedCards), as CheckCards applies them.
ALLOWED_CARDS = ('ocg', 'tcg', 'ocg_tcg', 'prerelease', 'any', 'ocg_custom', 'tcg_custom',
	'ocg_tcg_custom', 'prerelease_custom')


def allowed_cards_error(card, allowed):
	ot = card.ot
	if allowed in ('ocg', 'tcg', 'ocg_tcg'):
		if ot > 0x3:
			return UNOFFICIALCARD
		if allowed == 'ocg' and not ot & SCOPE_OCG:
			return TCGONLY
		if allowed == 'tcg' and not ot & SCOPE_TCG:
			return OCGONLY
		return 0
	need = dict(prerelease=SCOPE_OCG | SCOPE_TCG | SCOPE_PRERELEASE,
		ocg_custom=SCOPE_OCG | SCOPE_CUSTOM, tcg_custom=SCOPE_TCG | SCOPE_CUSTOM,
		ocg_tcg_custom=SCOPE_OCG | SCOPE_TCG | SCOPE_CUSTOM,
		prerelease_custom=SCOPE_OCG | SCOPE_TCG | SCOPE_PRERELEASE | SCOPE_CUSTOM).get(allowed)
	if need is not None and not ot & need:
		return UNOFFICIALCARD
	return 0


class Deck:
	def __init__(self, main=(), extra=(), side=(), master=None):
		self.main = list(main)     # codes
		self.extra = list(extra)
		self.side = list(side)
		self.master = master       # code or None


def check_deck(deck, lst, cards, allowed='any', forbidden_types=0, check_content=True):
	"""Domain deck check. Returns (error type, code) or (0, 0) when the deck is legal.

	Order (the first failing step is reported):
	  1. Deck Master present, known, a monster, not a Token, not a Skill -> 0x11
	     (code = DM code or 0). Always checked, also without content checks.
	  2. Deck Master not in "#@forbid-dm" (own code, then alias) -> 0x14.
	  3. Sizes, Deck Master not counted: Main 60 (Skills not counted), Extra 0-15,
	     Side 0 -> MAINCOUNT / EXTRACOUNT / SIDECOUNT (code 0).
	  4. Forbidden types (TYPE_SKILL is always forbidden in a Domain list) -> FORBTYPE.
	  5. Any card with the Rush or Legend scope bit, Deck Master included -> 0x12.
	  6. For DM, Main, Extra, Side in this order, card by card: unknown code ->
	     UNKNOWNCARD; allowed-cards scope -> UNOFFICIALCARD/OCGONLY/TCGONLY; a second
	     copy by canonical code (alias if != 0, else code) -> 0x13; ordinary list
	     lines (limit, whitelist) -> LFLIST.
	  7. Every Main and Extra card in the domain of the Deck Master -> else 0x12.
	Steps 2 and 4-7 are the content checks."""
	dm = cards.get(deck.master) if deck.master else None
	if dm is None or not dm.type & TYPE_MONSTER or dm.type & (TYPE_TOKEN | TYPE_SKILL):
		return DOMAIN_DECK_MASTER, deck.master or 0
	if check_content and is_forbidden_dm(lst, dm):
		return DOMAIN_FORBIDDEN_DM, dm.code
	skills = sum(1 for c in deck.main if c in cards and cards[c].type & TYPE_SKILL)
	for pile, err, (lo, hi), n in (('main', MAINCOUNT, DOMAIN_SIZES['main'], len(deck.main) - skills),
			('extra', EXTRACOUNT, DOMAIN_SIZES['extra'], len(deck.extra)),
			('side', SIDECOUNT, DOMAIN_SIZES['side'], len(deck.side))):
		if not lo <= n <= hi:
			return err, 0
	if not check_content:
		return 0, 0
	every = [deck.master] + deck.main + deck.extra + deck.side
	ftypes = forbidden_types | TYPE_SKILL
	for code in every:
		if code in cards and cards[code].type & ftypes:
			return FORBTYPE, code
	for code in every:
		if code in cards and cards[code].ot & (SCOPE_RUSH | SCOPE_LEGEND):
			return DOMAIN_OUT_OF_DOMAIN, code
	counts = {}
	for code in every:
		card = cards.get(code)
		if card is None:
			return UNKNOWNCARD, code
		err = allowed_cards_error(card, allowed)
		if err:
			return err, code
		canon = card.canonical()
		counts[canon] = counts.get(canon, 0) + 1
		if counts[canon] > 1:
			return DOMAIN_SINGLETON, code
		limit = lst.limitation(card)
		if (limit is not None and counts[canon] > limit) or (lst.whitelist and limit is None):
			return LFLIST, code
	dom = deck_master_domain(lst, dm)
	for code in deck.main + deck.extra:
		if in_domain(cards[code], dom, cards) is None:
			return DOMAIN_OUT_OF_DOMAIN, code
	return 0, 0


def read_ydk(path, cards):
	"""Read a .ydk: "#main"/"#extra" codes, "!side" codes, and the first code
	after "#master" as the Deck Master. Main and Extra are split by card type."""
	main, side, master = [], [], None
	section = 'main'
	with open(path, 'rb') as f:
		for raw in f.read().split(b'\n'):
			line = raw.strip()
			if not line:
				continue
			if line == b'#master':
				section = 'master'
				continue
			if line.startswith(b'#'):
				continue
			if line.startswith(b'!'):
				section = 'side'
				continue
			try:
				code = stoul(line) & M32
			except (ValueError, OverflowError):
				continue
			if section == 'master':
				if master is None:
					master = code
			elif section == 'side':
				side.append(code)
			else:
				main.append(code)
	extra = [c for c in main if c in cards and cards[c].type & TYPES_EXTRA and cards[c].type & TYPE_MONSTER]
	main = [c for c in main if c not in extra]
	return Deck(main, extra, side, master)


def domain_pool(cards):
	"""Monsters that can be put in a deck: not alternate artworks/treated-as rows,
	not Tokens."""
	return [c for c in sorted(cards.values(), key=lambda c: c.code)
		if c.alias == 0 and c.type & TYPE_MONSTER and not c.type & TYPE_TOKEN]


def count_domain(lst, dm, cards):
	dom = deck_master_domain(lst, dm)
	reasons = {}
	for x in domain_pool(cards):
		r = in_domain(x, dom, cards)
		reasons[r] = reasons.get(r, 0) + 1
	inside = sum(v for k, v in reasons.items() if k is not None)
	return inside, reasons


# ---------------------------------------------------------------------------
# Test vectors for other implementations
# ---------------------------------------------------------------------------

# Known FNV-1a 32-bit values.
FNV_VECTORS = ((b'', 0x811C9DC5), (b'a', 0xE40C292C), (b'foobar', 0xBF9CF968))

# A file with the corner cases of the format. Expected results: see selftest().
VECTOR_FILE = (
	b'#@dm 1 a=1\n'                         # before any list: comment
	b'$domain\n'                            # outside a list: ignored
	b'!Plain\n'
	b'#@dm 2 a=1\n'                         # not a Domain list: comment
	b'12345 1 --card\n'
	b'!Dom A\n'
	b'#@dm 3 a=2\n'                         # before "$domain": comment
	b'$domain\n'
	b'$domain\n'                            # second "$domain": ignored
	b'$genesys 100\n'                       # "$genesys" after "$domain": ignored
	b'#@dm 10 a=20 r=2 s=dd,10a2 n=46986414,89631139 \t \r\n'
	b'#@dm 10 a=1\n'                        # duplicate: hashed, first line wins
	b'#@dm 11 a= r= s= n=\n'
	b'#@dm 12 s=0,,1cf, x=7\n'              # zero/empty items and unknown keys ignored
	b'#@dm 13 a=zz\n'                       # malformed: hashed, skipped
	b'#@dm\n'                               # malformed
	b'#@\n'                                 # empty text: hashed
	b'#@forbid-dm 14\n'
	b'#@other 15\n'                         # unknown directive: hashed, skipped
	b'# @dm 16\n'                           # ordinary comment
	b'89631139 0 --Blue-Eyes White Dragon\r\n'
	b'!Gen\n'
	b'$genesys 100\n'
	b'$domain\n'                            # "$domain" after "$genesys": ignored
	b'#@dm 17\n'                            # not a Domain list: comment
	b'89631139 3 7 --Blue-Eyes White Dragon\n'
)


def selftest():
	for data, h in FNV_VECTORS:
		assert fnv1a32(data) == h, data
	lists = parse_lflist_bytes(VECTOR_FILE)
	assert [l.name for l in lists] == ['Plain', 'Dom A', 'Gen']
	plain, dom, gen = lists
	assert not plain.domain and plain.hash == BANLIST_HASH_MAGIC ^ card_line_salt(12345, 1)
	assert gen.genesys and not gen.domain and not gen.dm
	assert gen.hash == BANLIST_HASH_MAGIC ^ genesys_cap_salt(100) ^ card_line_salt(89631139, 3) ^ \
		genesys_points_salt(89631139, 7)
	assert dom.domain and not dom.genesys
	texts = [b'dm 10 a=20 r=2 s=dd,10a2 n=46986414,89631139', b'dm 10 a=1', b'dm 11 a= r= s= n=',
		b'dm 12 s=0,,1cf, x=7', b'dm 13 a=zz', b'dm', b'', b'forbid-dm 14', b'other 15']
	h = BANLIST_HASH_MAGIC ^ DOMAIN_SALT ^ card_line_salt(89631139, 0)
	for t in texts:
		h ^= domain_line_salt(t)
	assert dom.hash == h, hex(dom.hash)
	assert sorted(dom.dm) == [10, 11, 12] and dom.forbid_dm == {14}
	assert dom.dm[10] == DomainEntry(10, 0x20, 0x2, (0xDD, 0x10A2), (46986414, 89631139))
	assert dom.dm[11] == DomainEntry(11) and dom.dm[12] == DomainEntry(12, 0, 0, (0x1CF,))
	assert dom.malformed == [b'dm 13 a=zz', b'dm', b'', b'other 15']
	assert dom.content == {89631139: 0}
	return lists


# ---------------------------------------------------------------------------
# Command line
# ---------------------------------------------------------------------------

def _default_list():
	return os.path.join(os.path.dirname(os.path.abspath(__file__)), os.pardir, 'Domain.lflist.conf')


def main(argv=None):
	ap = argparse.ArgumentParser(description=__doc__.split('\n')[0])
	sub = ap.add_subparsers(dest='cmd', required=True)
	p = sub.add_parser('hash', help='print the hash of every list in the files')
	p.add_argument('files', nargs='*')
	p = sub.add_parser('selftest', help='check the hash primitives and the test vector file')
	p = sub.add_parser('vectors', help='write the test vector file and print its expected hashes')
	p.add_argument('out')
	p = sub.add_parser('show', help='print the parsed #@dm entry of a code')
	p.add_argument('list')
	p.add_argument('codes', nargs='+', type=int)
	for name in ('check', 'count'):
		p = sub.add_parser(name)
		p.add_argument('--babel', required=True, help='BabelCDB directory')
		p.add_argument('--list', default=_default_list())
		if name == 'check':
			p.add_argument('--allowed', choices=ALLOWED_CARDS, default='any')
			p.add_argument('decks', nargs='+')
		else:
			p.add_argument('codes', nargs='+', type=int)
	args = ap.parse_args(argv)
	if args.cmd == 'hash':
		for path in args.files or [_default_list()]:
			for lst in parse_lflist(path):
				kind = 'domain' if lst.domain else 'genesys' if lst.genesys else 'list'
				extra = ' dm=%d forbid-dm=%d malformed=%d' % (len(lst.dm), len(lst.forbid_dm), len(lst.malformed)) \
					if lst.domain else ''
				print('%s\t%s\t0x%08X\t%s cards=%d%s' % (path, lst.name, lst.hash, kind, len(lst.content), extra))
		return 0
	if args.cmd in ('selftest', 'vectors'):
		lists = selftest()
		if args.cmd == 'vectors':
			with open(args.out, 'wb') as f:
				f.write(VECTOR_FILE)
		for lst in lists:
			print('%s\t0x%08X\tdomain=%d genesys=%d dm=%s forbid-dm=%s' % (lst.name, lst.hash, lst.domain,
				lst.genesys, sorted(lst.dm), sorted(lst.forbid_dm)))
		print('selftest OK')
		return 0
	if args.cmd == 'show':
		lst = find_domain_list(args.list)
		for code in args.codes:
			print(lst.dm.get(code))
		return 0
	lst = find_domain_list(args.list)
	cards = load_cards(babel_cdbs(args.babel))
	if args.cmd == 'count':
		for code in args.codes:
			dm = cards[code]
			inside, reasons = count_domain(lst, dm, cards)
			print('%d %s: %d of %d monsters in domain %s' % (code, dm.name, inside, len(domain_pool(cards)),
				{k or 'out': v for k, v in sorted(reasons.items(), key=lambda kv: kv[0] or '~')}))
		return 0
	status = 0
	for path in args.decks:
		err, code = check_deck(read_ydk(path, cards), lst, cards, args.allowed)
		if err:
			status = 1
			print('%s: %s (0x%X) code %d %s' % (path, ERROR_NAMES[err], err, code,
				cards[code].name if code in cards else ''))
		else:
			print('%s: OK' % path)
	return status


if __name__ == '__main__':
	sys.exit(main())

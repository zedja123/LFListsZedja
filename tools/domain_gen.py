#!/usr/bin/env python3
"""Generate Domain.lflist.conf, the card pool data of the Domain format.

For every Main and Extra Deck monster that can be a Deck Master, the tool
writes one "#@dm" line with the complete Domain of that card (Domain format
rulebook v1.4):

  a  Attributes: its own and every Attribute named in its effect text
  r  Types: its own and every Type named in its effect text
  s  archetypes: its own and every archetype named in its effect text,
     including the archetypes of the monsters it names, after the base
     archetype reduction (see reduce_archetypes)
  n  the monsters named in its effect text (Spells and Traps are left out,
     they are always in every Domain)

Token definitions count, because their Attribute and Type are part of the text.
Normal monster flavor text, "(This card is not/always treated as ...)"
reminders and the card's own name do not count. A quoted Spell or Trap name
names that card only, unless "card(s)", "monster(s)", "Spell" or "Trap"
(optionally after a card kind: "Link Monster", "Equip Spell") follows it; then
it is an archetype name. Plural forms ("Hyenas", "Servant(s) of Endymion")
and a few old or regional names (RENAMED_CARDS, ARCHETYPE_NAME_ALIASES) are
resolved too.

Lines are keyed by the card's own code: one for every monster row without an
alias, and one for every row whose alias has a different name ("always treated
as" cards); none for alternate artworks. Output is sorted by code and depends
only on the inputs.

Inputs: the BabelCDB databases cards.cdb, release-*.cdb and prerelease-*.cdb
(never the Rush, Skill, unofficial or GOAT ones) and the CardScripts file
archetype_setcode_constants.lua (archetype names and the list of known
archetype codes). The official scripts' s.listed_names / s.listed_series are
only read by --report, to compare them with the text.

Usage:
  domain_gen.py --babel <BabelCDB dir> --scripts <CardScripts dir> [-o Domain.lflist.conf]
  domain_gen.py ... --check            exit 1 if the output file is not up to date
  domain_gen.py ... --explain <code|name>...   print how a Domain was built
  domain_gen.py ... --report           print unresolved quotes and script differences
"""
import argparse
import importlib.util
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))


def _load_ref():
	spec = importlib.util.spec_from_file_location('domain_ref', os.path.join(HERE, 'domain_ref.py'))
	mod = importlib.util.module_from_spec(spec)
	spec.loader.exec_module(mod)
	return mod


ref = _load_ref()

TYPE_MONSTER = 0x1
TYPE_SPELL = 0x2
TYPE_TRAP = 0x4
TYPE_NORMAL = 0x10
TYPE_EFFECT = 0x20
TYPE_TOKEN = 0x4000
TYPE_PENDULUM = 0x1000000
TYPE_SKILL = 0x8000000

ATTRIBUTES = {'EARTH': 0x1, 'WATER': 0x2, 'FIRE': 0x4, 'WIND': 0x8, 'LIGHT': 0x10, 'DARK': 0x20, 'DIVINE': 0x40}
RACES = {
	'Warrior': 0x1, 'Spellcaster': 0x2, 'Fairy': 0x4, 'Fiend': 0x8, 'Zombie': 0x10, 'Machine': 0x20,
	'Aqua': 0x40, 'Pyro': 0x80, 'Rock': 0x100, 'Winged Beast': 0x200, 'Plant': 0x400, 'Insect': 0x800,
	'Thunder': 0x1000, 'Dragon': 0x2000, 'Beast': 0x4000, 'Beast-Warrior': 0x8000, 'Dinosaur': 0x10000,
	'Fish': 0x20000, 'Sea Serpent': 0x40000, 'Reptile': 0x80000, 'Psychic': 0x100000,
	'Divine-Beast': 0x200000, 'Creator God': 0x400000, 'Wyrm': 0x800000, 'Cyberse': 0x1000000,
	'Illusion': 0x2000000,
}
RACE_WORDS = dict(RACES, Fairies=RACES['Fairy'])

# Attributes are written in capitals; Types match the longest name first, with an
# optional "-Type" and plural "s" ("Winged Beast-Type", "Dragons", "Beast-Warriors").
ATTRIBUTE_RE = re.compile(r'(?<![A-Za-z])(' + '|'.join(ATTRIBUTES) + r')(?![A-Za-z])')
RACE_RE = re.compile(r'(?<![\w-])(' + '|'.join(sorted(map(re.escape, RACE_WORDS), key=len, reverse=True))
	+ r')(?:-Type)?s?(?![\w-])')
QUOTE_RE = re.compile(r'"([^"]+)"')
PLACEHOLDER_RE = re.compile(r'#(\d+)#')
# "(This card is not treated as ...)", "(This card is always treated as ...)",
# "(This card's name is always treated as ...)", "(... also always treated as ...)".
REMINDER_RE = re.compile(r"\(\s*This card(?:'s name)? is (?:not|always|also always) (?:treated|considered) as[^)]*\)",
	re.I)
UNOFFICIAL_RE = re.compile(r'\* The above text is unofficial.*$', re.S)
# What makes a quoted Spell/Trap name an archetype (amendment D8): "card(s)",
# "monster(s)", "Spell", "Trap", also after a card kind ("Link Monster", "Equip Spell").
ARCHETYPE_FOLLOW_RE = re.compile(r'\s*(?:(?:Effect|Normal|Fusion|Ritual|Synchro|Xyz|Pendulum|Link|Tuner|Flip|Gemini|'
	r'Spirit|Union|Toon|Equip|Field|Continuous|Quick-Play|Counter)\s+)*(?:cards?|monsters?|Spells?|Traps?)\b', re.I)
# Names in card texts that differ from the current card name or constant name.
# Old card names: quoted name -> current name.
RENAMED_CARDS = {
	'Frog the Jam': 'Slime Toad',
}
# Archetype names whose constant is named after the other region's name.
ARCHETYPE_NAME_ALIASES = {
	'True Draco': 'SET_TRUE_DRACO_KING',
	'True King': 'SET_TRUE_DRACO_KING',
	'Goblin Biker': 'SET_GOBLIN_RIDER',
}


def norm(name):
	"""Archetype name key: letters and digits only, upper case
	("R.B." -> "RB", "Blue-Eyes" -> "BLUEEYES", SET_DESTINY_HERO -> "DESTINYHERO")."""
	return re.sub(r'[^A-Z0-9]', '', name.upper())


def load_set_constants(path):
	consts = {}
	with open(path, encoding='utf-8') as f:
		for m in re.finditer(r'^(SET_\w+)\s*=\s*(0x[0-9a-fA-F]+|\d+)', f.read(), re.M):
			consts[m.group(1)] = int(m.group(2), 0)
	if not consts:
		raise SystemExit('%s: no SET_ constants found' % path)
	return consts


class Generator:
	def __init__(self, cards, set_constants):
		self.cards = cards
		self.known_sets = frozenset(set_constants.values())
		self.archetype_names = {}
		for name, value in set_constants.items():
			self.archetype_names.setdefault(norm(name[4:]), set()).add(value)
		for name, const in ARCHETYPE_NAME_ALIASES.items():
			if const in set_constants:
				self.archetype_names.setdefault(norm(name), set()).add(set_constants[const])
		# Card names (Tokens excluded): rows without alias, and rows whose alias has
		# another name ("always treated as", D9). A name maps to its row with the
		# lowest code; alternate artworks share the name of their alias row.
		self.by_name = {}
		for card in sorted(cards.values(), key=lambda c: (c.alias != 0, c.code)):
			if card.type & TYPE_TOKEN or card.type & TYPE_SKILL or not self.has_own_name(card):
				continue
			self.by_name.setdefault(card.name, card.code)
		self.quoted_names = sorted((n for n in self.by_name if '"' in n), key=len, reverse=True)

	def has_own_name(self, card):
		if card.alias == 0:
			return True
		target = self.cards.get(card.alias)
		return target is None or target.name != card.name

	def deck_masters(self):
		"""Rows that get a #@dm line (amendment D1)."""
		return [c for c in sorted(self.cards.values(), key=lambda c: c.code)
			if c.type & TYPE_MONSTER and not c.type & (TYPE_TOKEN | TYPE_SKILL) and self.has_own_name(c)]

	def reduce_archetypes(self, codes):
		"""Base archetype reduction. A sub-archetype code (with bits in 0xf000) becomes
		its base (code & 0xfff) when the base is a known archetype constant
		(Destiny HERO 0xc008 -> HERO 0x8). Otherwise a code with several sub-archetype
		bits is split into the single-bit codes that are known constants (Dark
		Magician Girl 0x30a2 -> Dark Magician 0x10a2 and Magician Girl 0x20a2); every
		such code matches all cards of the original one. Anything else stays."""
		out = set()
		for v in codes:
			base, sub = v & 0xFFF, v & 0xF000
			if sub and base in self.known_sets:
				out.add(base)
			elif bin(sub).count('1') > 1:
				parts = {base | b for b in (0x1000, 0x2000, 0x4000, 0x8000) if sub & b and (base | b) in self.known_sets}
				out |= parts or {v}
			else:
				out.add(v)
		return out

	def effect_text(self, card):
		"""The text that counts: no unofficial-translation note, no flavor text of
		Normal monsters (Pendulum Normals keep their Pendulum Effect), no reminders."""
		text = UNOFFICIAL_RE.sub('', card.desc).replace('\r', '')
		if card.type & TYPE_NORMAL and not card.type & TYPE_EFFECT:
			if card.type & TYPE_PENDULUM and '----' in text:
				text = text.split('----')[0]
			else:
				return ''
		return REMINDER_RE.sub(' ', text)

	def domain(self, card):
		"""Returns (attribute, race, archetypes, names, details)."""
		text = self.effect_text(card)
		# Protect card names that contain quotes (Therion "King" Regulus).
		for name in self.quoted_names:
			if name in text:
				text = text.replace('"%s"' % name, '"#%d#"' % self.by_name[name])
		bare = QUOTE_RE.sub(' ', text)
		attribute = card.attribute
		race = card.race
		for word in ATTRIBUTE_RE.findall(bare):
			attribute |= ATTRIBUTES[word]
		for word in RACE_RE.findall(bare):
			race |= RACE_WORDS[word]
		archetypes = self.reduce_archetypes(ref.card_archetypes(card, self.cards))
		names = set()
		details = dict(text=text, quotes=[], unresolved=[], spell_trap=[])
		for m in QUOTE_RE.finditer(text):
			quote = m.group(1)
			pm = PLACEHOLDER_RE.fullmatch(quote)
			if pm:
				quote = self.cards[int(pm.group(1))].name
			if quote.endswith('(s)'):
				quote = quote[:-3]
			if quote == card.name:
				continue
			follow = ARCHETYPE_FOLLOW_RE.match(text, m.end()) is not None
			# Exact text first; then without "(s)" and plural endings ("Hyenas").
			variants = [quote, quote.replace('(s)', '')]
			if quote.endswith('es'):
				variants.append(quote[:-2])
			if quote.endswith('s'):
				variants.append(quote[:-1])
			for variant in variants:
				result = self.resolve(variant, follow)
				if result is not None:
					break
			if result is None:
				details['unresolved'].append(quote)
				continue
			code, arch = result
			if code is None and not arch:
				details['spell_trap'].append(quote)
				continue
			details['quotes'].append(quote)
			if code is not None and code != card.code:
				names.add(code)
			archetypes |= arch
		return attribute, race & ref.M64, archetypes, names, details

	def resolve(self, quote, follow):
		"""What a quoted string names: (monster code or None, archetypes), or None if
		it is neither a card nor an archetype. A monster brings its archetypes; a Spell
		or Trap name names only that card (D8), which is in every Domain anyway,
		unless a word like "card", "monster", "Spell" or "Trap" follows it."""
		quote = RENAMED_CARDS.get(quote, quote)
		code = self.by_name.get(quote)
		arch = self.archetype_names.get(norm(quote))
		if code is not None:
			named = self.cards[code]
			if named.type & TYPE_MONSTER:
				return code, self.reduce_archetypes(ref.card_archetypes(named, self.cards)) | \
					self.reduce_archetypes(arch or ())
			if not follow:
				return None, set()
		if arch:
			return None, self.reduce_archetypes(arch)
		return (None, set()) if code is not None else None

	def line(self, card):
		attribute, race, archetypes, names, _ = self.domain(card)
		out = '#@dm %d' % card.code
		if attribute:
			out += ' a=%x' % attribute
		if race:
			out += ' r=%x' % race
		if archetypes:
			out += ' s=' + ','.join('%x' % v for v in sorted(archetypes))
		if names:
			out += ' n=' + ','.join(str(v) for v in sorted(names))
		return out


HEADER = """#[Domain]
!Domain 1.4
$domain
#Domain format v1.4 (fan-made): 1 Deck Master, a 60-card Main Deck, up to 15 Extra Deck cards,
#1 copy of each card, and every Main/Extra Deck card within the Domain of the Deck Master.
#Data lines (older clients and servers read them as comments):
#  "#@forbid-dm <code>" forbids a card as Deck Master.
#  "#@dm <code> a=<attributes> r=<types> s=<archetypes> n=<codes>" is the complete Domain of a
#  Deck Master: a and r are masks and s 16-bit archetype codes, all hexadecimal; n are the
#  monsters named in its text, decimal. Without a line the Domain is the card's own Attribute,
#  Type and archetypes. Spells, Traps and DIVINE/Divine-Beast monsters are in every Domain.
#Ordinary card lines are the Forbidden Cards. The rulebook forbids no card and no Deck Master.
#Generated by tools/domain_gen.py from BabelCDB and CardScripts; do not edit the data lines.
"""


def render(gen):
	lines = [gen.line(c) for c in gen.deck_masters()]
	codes = [int(l.split()[1]) for l in lines]
	assert len(codes) == len(set(codes)), 'duplicate #@dm code'
	return HEADER + ''.join(l + '\n' for l in lines)


def verify(gen, content):
	"""Parse the output with the reference parser: hash checks (D7) and round trip."""
	lists = ref.parse_lflist_bytes(content.encode('utf-8'))
	assert len(lists) == 1 and lists[0].domain, 'expected exactly one Domain list'
	lst = lists[0]
	assert not lst.malformed, 'malformed #@ lines: %r' % lst.malformed[:3]
	assert lst.hash not in (0, ref.BANLIST_HASH_MAGIC), 'unusable list hash 0x%08X' % lst.hash
	# No intermediate hash may be 0 either (older code used hash 0 as "no list").
	h = ref.BANLIST_HASH_MAGIC ^ ref.DOMAIN_SALT
	for raw in content.encode('utf-8').split(b'\n'):
		if raw.startswith(b'#@'):
			h ^= ref.domain_line_salt(raw[2:].rstrip(b' \t'))
			assert h != 0, 'intermediate hash 0'
	assert h == lst.hash
	for card in gen.deck_masters():
		attribute, race, archetypes, names, _ = gen.domain(card)
		assert lst.dm[card.code] == ref.DomainEntry(card.code, attribute, race, sorted(archetypes), names), card.code
	return lst


def listed_in_script(scripts_dir, code, card_consts, set_consts):
	path = os.path.join(scripts_dir, 'official', 'c%d.lua' % code)
	if not os.path.exists(path):
		return None
	with open(path, encoding='utf-8', errors='replace') as f:
		src = f.read()
	out = {}
	for key, consts in (('listed_names', card_consts), ('listed_series', set_consts)):
		vals = set()
		for m in re.finditer(r's\.%s\s*=\s*\{([^}]*)\}' % key, src):
			for tok in re.split(r'[,\s]+', m.group(1)):
				if tok == 'id':
					vals.add(code)
				elif re.fullmatch(r'0x[0-9a-fA-F]+|\d+', tok):
					vals.add(int(tok, 0))
				elif tok in consts:
					vals.add(consts[tok])
		out[key] = vals
	return out


def report(gen, scripts_dir, set_consts):
	card_consts = {}
	with open(os.path.join(scripts_dir, 'card_counter_constants.lua'), encoding='utf-8') as f:
		for m in re.finditer(r'^(CARD_\w+)\s*=\s*(0x[0-9a-fA-F]+|\d+)', f.read(), re.M):
			card_consts[m.group(1)] = int(m.group(2), 0)
	unresolved = {}
	names_missing = series_missing = 0
	for card in gen.deck_masters():
		_, _, archetypes, names, det = gen.domain(card)
		for q in det['unresolved']:
			unresolved.setdefault(q, []).append(card.code)
		lst = listed_in_script(scripts_dir, card.code, card_consts, set_consts)
		if lst is None:
			continue
		ln = {c for c in lst['listed_names'] if c in gen.cards and c != card.code
			and gen.cards[c].type & TYPE_MONSTER and not gen.cards[c].type & TYPE_TOKEN}
		canon = {gen.cards[c].canonical() for c in names} | names
		miss = {c for c in ln if c not in canon and gen.cards[c].canonical() not in canon}
		if miss:
			names_missing += 1
			print('listed_names not in text: %d %s -> %s' % (card.code, card.name,
				', '.join('%d %s' % (c, gen.cards[c].name) for c in sorted(miss))))
		smiss = {s for s in lst['listed_series']
			if not any(ref.match_setcode(d, s) for d in archetypes)}
		if smiss:
			series_missing += 1
			print('listed_series not covered: %d %s -> %s' % (card.code, card.name,
				','.join('%x' % s for s in sorted(smiss))))
	for q in sorted(unresolved):
		print('unresolved quote: "%s" in %s' % (q, ','.join(str(c) for c in unresolved[q][:8])))
	print('summary: %d unresolved quotes in %d cards; %d cards with listed_names not in text; '
		'%d cards with listed_series not covered' % (len(unresolved),
		len({c for v in unresolved.values() for c in v}), names_missing, series_missing))


def explain(gen, lst, key):
	if key.isdigit():
		card = gen.cards[int(key)]
	else:
		card = gen.cards[gen.by_name[key]]
	attribute, race, archetypes, names, det = gen.domain(card)
	print('%d %s' % (card.code, card.name))
	print('  line:       %s' % gen.line(card))
	print('  own:        a=%x r=%x setcodes=%s' % (card.attribute, card.race,
		','.join('%x' % v for v in card.setcodes())))
	print('  quotes:     %s' % det['quotes'])
	print('  spell/trap: %s' % det['spell_trap'])
	print('  unresolved: %s' % det['unresolved'])
	print('  names:      %s' % ', '.join('%d %s' % (c, gen.cards[c].name) for c in sorted(names)))
	inside, reasons = ref.count_domain(lst, card, gen.cards)
	print('  monsters in domain: %d of %d %s' % (inside, len(ref.domain_pool(gen.cards)),
		{k or 'out': v for k, v in sorted(reasons.items(), key=lambda kv: kv[0] or '~')}))


def main(argv=None):
	ap = argparse.ArgumentParser(description=__doc__.split('\n')[0])
	ap.add_argument('--babel', required=True, help='BabelCDB directory (cards.cdb, release-*.cdb, prerelease-*.cdb)')
	ap.add_argument('--scripts', required=True, help='CardScripts directory (archetype_setcode_constants.lua)')
	ap.add_argument('-o', '--output', default=os.path.join(HERE, os.pardir, 'Domain.lflist.conf'))
	ap.add_argument('--check', action='store_true', help='do not write; exit 1 if the output is not up to date')
	ap.add_argument('--explain', nargs='+', metavar='CODE|NAME')
	ap.add_argument('--report', action='store_true')
	args = ap.parse_args(argv)
	set_consts = load_set_constants(os.path.join(args.scripts, 'archetype_setcode_constants.lua'))
	cards = ref.load_cards(ref.babel_cdbs(args.babel))
	gen = Generator(cards, set_consts)
	content = render(gen)
	lst = verify(gen, content)
	if args.report:
		report(gen, args.scripts, set_consts)
	if args.explain:
		for key in args.explain:
			explain(gen, lst, key)
	if args.check:
		try:
			with open(args.output, encoding='utf-8', newline='') as f:
				current = f.read()
		except OSError:
			current = None
		if current != content:
			print('%s is not up to date' % args.output, file=sys.stderr)
			return 1
	elif not args.explain and not args.report:
		with open(args.output, 'w', encoding='utf-8', newline='\n') as f:
			f.write(content)
	print('%d Deck Master lines, list hash 0x%08X' % (len(lst.dm), lst.hash), file=sys.stderr)
	return 0


if __name__ == '__main__':
	sys.exit(main())

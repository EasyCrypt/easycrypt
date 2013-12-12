#! /usr/bin/env python

# --------------------------------------------------------------------
import sys, os, re

# --------------------------------------------------------------------
class codetx(object):
    def __call__(self, code):
        raise RuntimeError()

# --------------------------------------------------------------------
class WordRename(codetx):
    def __init__(self, map_):
        self._map = map_

    def __call__(self, code):
        kwre = [re.escape(x) for x in self._map.keys()]
        kwre = r'\b(%s)\b' % ('|'.join(kwre),)

        def subkw(m):
            return self._map[m.group(1)]
        
        return re.sub(kwre, subkw, code)

# --------------------------------------------------------------------
class OracleInfo(codetx):
    def __init__(self):
        pass

    def __call__(self, code):
        return re.sub(r'\bproc\b(.*?){\s*\*', 'proc *\\1{', code)

# --------------------------------------------------------------------
class DatatypeToType(codetx):
    def __init__(self):
        pass

    def __call__(self, code):
        return \
            re.sub(r'\bdatatype\b(.*?)=(.*?)\.(:?\s|$)',
                   'type\\1= [\\2].\\3',
                   code, 0, re.S)

# --------------------------------------------------------------------
class ProofMode(codetx):
    def __init__(self):
        pass

    def __call__(self, code):
        return re.sub(r'\bproof\b\s*\.', 'proof -strict.', code)

# --------------------------------------------------------------------
class PrRw(codetx):
    def __init__(self):
        pass

    def __call__(self, code):
        return \
            re.sub(r'\brewrite\s+Pr\b\s*(\w+)',
                   'rewrite Pr[\\1]',
                   code)

# --------------------------------------------------------------------
class CPred(codetx):
    def __init__(self):
        pass

    def __call__(self, code):
        return re.sub(r"('?\w+)\s+(\w+\.)*cpred\b", '(\\1 -> bool)', code)

# --------------------------------------------------------------------
ALLTX = [
    WordRename({'fun': 'proc', 'lambda' : 'fun'}),
    OracleInfo(),
    WordRename({'eqobs_in': 'sim'}),
    DatatypeToType(),
    WordRename({'record': 'type'}),
    WordRename({'save': 'qed'}),
    WordRename({'bd_hoare': 'phoare', 'bdhoare_deno': 'phoare_deno'}),
    ProofMode(),
    WordRename({'phoare_deno': 'byphoare', 'equiv_deno': 'byequiv'}),
    WordRename({'pr_false': 'trivial'}),
    PrRw(),
    WordRename({'xor_comm': 'xorC',
                'xor_associative': 'xorA',
                'xor_nilpotent': 'xorK'}),
    CPred(),
]

ALLTX = [ALLTX[-1]]

# --------------------------------------------------------------------
def for1(filename):
    with open(filename, 'rb') as stream:
        doc = stream.read()

    for tx in ALLTX:
        doc = tx(doc)

    os.rename(filename, filename + '~')
    with open(filename, 'wb') as stream:
        stream.write(doc)

# --------------------------------------------------------------------
def _main():
    for filename in sys.argv[1:]:
        for1(filename)

# --------------------------------------------------------------------
if __name__ == '__main__':
    _main()

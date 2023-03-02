import ply.lex as lex
import sys

class LexerPySMT(object):
    tokens = [
        'NUM',
        'ID',
        'ATRIB', # = 
        'OR', # ||
        'AND', # &&
        'EQ', # == 
        'LEQ',  # <= - (less or equal)
        'GEQ',  # >= - (greater or equal)
        'GT',   # >  - (greater than)
        'LT',   # <  - (less than)
        'NEQ',  # != - (not equal -> NEQ -> NECC)
        'NOT',  # !  - (not)
        'LCBracket',
        'RCBracket',
        'SUM',
        'SUB',
        'DIV',
        'MULT',
        'MOD'
    ]

    literals = [';']

    t_NEQ = r'\!\='
    t_NOT = r'\!'
    t_OR = r'\|\|'
    t_AND = r'\&\&'
    t_MOD = r'\%'
    t_SUM = r'\+'
    t_SUB = r'\-'
    t_DIV = r'\/'
    t_MULT = r'\*'
    t_LEQ = r'\<\='
    t_GEQ = r'\>\='
    t_GT = r'\>'
    t_LT = r'\<'
    t_EQ = r'\=\='
    t_ATRIB = r'\='

    def t_NUM(self, t):
        r'\d+'
        return t
    
    def t_ID(self, t):
        r'\w+'
        return t

    t_LCBracket = r'\('
    t_RCBracket = r'\)'
    t_ignore = ' '



    def __init__(self, debug=0, optimize=0, lextab='lextab', reflags=0):
        self.lexer = lex.lex(module=self, debug=debug, optimize=optimize, lextab=lextab, reflags=reflags)
        self.token_stream = None

    def input(self, s):
        self.lexer.paren_count = 0
        self.lexer.input(s)

    def token(self):
        try:
            return next(self.token_stream)
        except StopIteration:
            return None
        
    def t_error(self, t):
        print("Illegal character '%s'" % t.value[0])
        t.lexer.skip(1)
        return

with open(f"tests/{sys.argv[1]}.txt") as f:
    content = f.read()
    print(content)

lexer = LexerPySMT()
lexer.input(content)


for token in lexer.lexer:
    print(f"({repr(token.type)} {repr(token.value)})")
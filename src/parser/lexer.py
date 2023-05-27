import ply.lex as lex
import sys

class LexerPySMT(object):
    reserved = {
        'pc' : 'PC'
    }

    tokens = [
        'NUM',
        'ID',
        'ATRIB', # =
        'OR',    # ||
        'AND',   # &&
        'EQ',    # == 
        'LEQ',   # <= - (less or equal)
        'GEQ',   # >= - (greater or equal)
        'GT',    # >  - (greater than)
        'LT',    # <  - (less than)
        'NEQ',   # != - (not equal -> NEQ -> NECC)
        'NOT',   # !  - (not)
        'LParen',
        'RParen',
        'SUM',
        'SUB',
        'DIV',
        'MULT',
        'MOD'
    ] + list(reserved.values())

    literals = [';']

    t_NEQ = r'\!\='
    t_NOT = r'\!'
    t_OR = r'\|\|'
    t_AND = r'\&\&'
    t_SUM = r'\+'
    t_SUB = r'\-'
    t_MULT = r'\*'
    t_DIV = r'\/'
    t_MOD = r'\%'
    t_LEQ = r'\<\='
    t_GEQ = r'\>\='
    t_GT = r'\>'
    t_LT = r'\<'
    t_EQ = r'\=\='
    t_ATRIB = r'\='
    t_LParen = r'\('
    t_RParen = r'\)'

    def t_NUM(self, t):
        r'\d+'
        return t
    
    def t_ID(self, t):
        r'\w+'
        if t.value == 'pc':
            raise Exception('pc is a reserved word')
        return t

    t_ignore = ' \n\t\r'

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
        return None


if __name__ == "__main__":
    with open(f"tests/{sys.argv[1]}.txt") as f:
        content = f.read()
        print(content)

    lexer = LexerPySMT()
    lexer.input(content)

    for token in lexer.lexer:
        print(f"({repr(token.type)} {repr(token.value)})")

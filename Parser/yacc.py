from lexer import LexerPySMT
import ast
import ply.yacc as yacc
import sys

# ---------------- Programa Simples----------------
class ParserPySMT(object):
    def __init__(self):
        self.arith_map = {
            "+": "BVAdd",
            "-": "BVSub",
            "*": "BVMul",
            "/": "BVDiv",
            "%": "BVURem",
        }
        self.precedence = (
            ('left', 'SUM', 'SUB'),
            ('left', 'MULT', 'DIV', 'MOD'),
        )
        self.tokens = LexerPySMT.tokens
        self.lexer = LexerPySMT()
        self.parser = yacc.yacc(start="Init", module=self)
    
    def compile(self, code):
        self.parser.PySMT = ""
        self.parser.parse(code, lexer=self.lexer.lexer)
        return self.parser.PySMT

    def p_Init(self, p):
        """Init : Cond
                | Atribs"""
        self.parser.PySMT = f"{p[1]}"

    bool_map = {
        ">": "BVUGT",
        "<": "BVULT",
        ">=": "BVUGE",
        "<=": "BVULE",
        "==": "EqualsOrIff",
        "!=": "NotEquals",
        "&&": "And",
        "||": "Or"
    }
    
    def p_Cond(self, p):
        """Cond : Expre GT Expre
                | Expre LT Expre
                | Expre GEQ Expre
                | Expre LEQ Expre
                | Expre EQ Expre
                | Expre NEQ Expre
                | Cond OR Cond
                | Cond AND Cond"""
        p[0] = f"{self.bool_map[p[2]]}({p[1]}, {p[3]})"
    
    def p_Cond_Not(self, p):
        """Cond : NOT Cond"""
        p[0] = f"Not({p[2]})"
    
    def p_Cond_Paren(self, p):
        """Cond : LParen Cond RParen"""
        p[0] = f"({p[2]})"

    def p_Atribs(self, p):
        """Atribs : Atrib ';'
                  | Atribs Atrib ';'"""
        if len(p) == 3:
            p[0] = f"{p[1]}"
        else:
            p[0] = f"And({p[1]},{p[2]})"
        
    def p_Atrib(self, p):
        """Atrib : ID ATRIB Expre"""
        p[0] = f"Equals(prox['{p[1]}'], {p[3]})"

    def p_Expre(self, p):
        """Expre : Expre SUM Expre
                 | Expre SUB Expre
                 | Expre MULT Expre
                 | Expre DIV Expre
                 | Expre MOD Expre"""
        p[0] = f"{self.arith_map[p[2]]}({p[1]}, {p[3]})"

    def p_Expre_Paren(self, p):
        """Expre : LParen Expre RParen"""
        p[0] = f"({p[2]})"

    def p_Expre_ID(self, p):
        """Expre : ID"""
        p[0] = f"curr['{p[1]}']"

    def p_Expre_NUM(self, p):
        """Expre : NUM"""
        p[0] = f"BV({p[1]}, 16)"

    def p_error(self, p):
        print('Syntax error!\np -> ', p)
        self.parser.sucesso = False


with open(f"tests/{sys.argv[1]}.txt") as f:
    content = f.read()

text = ParserPySMT().compile(content)

print(text)
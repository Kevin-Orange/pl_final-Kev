use crate::token::Token;
use crate::parser::Parser;
use crate::mtree::MTree;
use std::rc::Rc;

pub struct BindingPower {
    pub left: isize,
    pub right: isize,
    pub unary: isize,
}

impl Token {
    pub fn is_prefix_operator(&self) -> bool {
        match self {
            | Token::NOT
            | Token::SUB
            | Token::DIV => true,
            _ => false
        }
    }

    pub fn is_id(&self) -> bool {
        match self {
            Token::ID { .. } => true,
            _ => false
        }
    }

    pub fn is_value_atom(&self) -> bool {
        match self {
            Token::LIT_INT32 { .. }
            | Token::LIT_FLT32 { .. }
            | Token::LIT_CHAR { .. }
            | Token::LIT_BOOL { .. }
            | Token::LIT_STRING { .. } => true,
            _ => false
        }
    }

    pub fn binding_power(&self) -> BindingPower {
        match self {
            Token::EOI => BindingPower { left: 0, right: 0, unary: 0 },
            Token::ID { .. } => BindingPower { left: 0, right: 0, unary: 0 },

            Token::LIT_CHAR { .. } => BindingPower { left: 0, right: 0, unary: 0 },
            Token::LIT_INT32 { .. } => BindingPower { left: 0, right: 0, unary: 0 },
            Token::LIT_FLT32 { .. } => BindingPower { left: 0, right: 0, unary: 0 },
            Token::LIT_BOOL { .. } => BindingPower { left: 0, right: 0, unary: 0 },
            Token::LIT_STRING { .. } => BindingPower { left: 0, right: 0, unary: 0 },

            Token::ASSIGN => BindingPower { left: 5, right: 4, unary: 0 },


            Token::OR => BindingPower { left: 10, right: 11, unary: 0 },
            Token::AND => BindingPower { left: 11, right: 12, unary: 0 }, 
            Token::NOT => BindingPower { left: 18, right: 19, unary: 100 },

            Token::LT => BindingPower { left: 30, right: 30, unary: 0 },
            Token::GT => BindingPower { left: 30, right: 30, unary: 0 },
            Token::NLT => BindingPower { left: 30, right: 30, unary: 0 },
            Token::NGT => BindingPower { left: 30, right: 30, unary: 0 },
            Token::EQ => BindingPower { left: 30, right: 30, unary: 0 },
            Token::NEQ => BindingPower { left: 30, right: 30, unary: 0 },

            Token::ADD =>  BindingPower { left: 30, right: 31, unary: 0 },
            Token::SUB =>  BindingPower { left: 30, right: 31, unary: 100 }, 
            Token::MUL =>  BindingPower { left: 31, right: 32, unary: 0 },           
            Token::DIV =>  BindingPower { left: 31, right: 32, unary: 100 },


            Token::PARENS_L => BindingPower { left: 0, right: 0, unary: 0 },
            Token::PARENS_R => BindingPower { left: 0, right: 0, unary: 0 },
            Token::BRACKET_L => BindingPower { left: 0, right: 0, unary: 0 },
            Token::BRACKET_R => BindingPower { left: 0, right: 0, unary: 0 },
            Token::BRACE_L => BindingPower { left: 0, right: 0, unary: 0 },
            Token::BRACE_R => BindingPower { left: 0, right: 0, unary: 0 },

            Token::POINT => BindingPower { left: 0, right: 0, unary: 0 },
            Token::COMMA => BindingPower { left: 0, right: 0, unary: 0 },
            Token::COLON => BindingPower { left: 0, right: 0, unary: 0 },
            Token::SEMICOLON => BindingPower { left: 0, right: 0, unary: 0 },
            Token::ARROW_R => BindingPower { left: 0, right: 0, unary: 0 },

            // others: keywords, meta
            _ => BindingPower { left: 0, right: 0, unary: 0 }
            
        }
    }
}

impl Parser {
    pub fn parse_expr(&mut self) -> MTree {
        self.indent_print("parse_expr()");
        self.indent_increment();
        let tree = self.parse_expr_tok(1);
        self.indent_decrement();
        tree
    }

    pub fn parse_expr_tok(&mut self, rbl: isize) -> MTree {
        let token = self.curr();

        if token.is_prefix_operator() {
            let tree_prefix = self.parse_expr_prefix();
            self.parse_expr_infix(tree_prefix, rbl)
        } else if token == Token::PARENS_L {
            let tree_parens = self.parse_expr_parentheses();
            self.parse_expr_infix(tree_parens, rbl)
        } else if token.is_id() || token.is_value_atom() {
            let tree_atom = self.parse_expr_atom();
            self.parse_expr_infix(tree_atom, rbl)
        } else {
            MTree::new(Token::ERROR)
        }
    }

    pub fn parse_expr_prefix(&mut self) -> MTree {
        let token = self.curr();
        self.advance();
        let tree = self.parse_expr_tok(token.binding_power().unary );
        MTree {
            token,
            children: vec![Rc::new(tree)]
        }
    }


    pub fn parse_expr_parentheses(&mut self) -> MTree {
        self.expect(Token::PARENS_L);
        let tree = self.parse_expr();
        self.expect(Token::PARENS_R);
        tree
    }

    pub fn parse_expr_atom(&mut self) -> MTree {
        let atom = self.curr();
        self.advance();
        if self.peek(Token::PARENS_L) {
            self.parse_expr_call(atom)
        } else {
            MTree::new(atom)
        }
    }


    pub fn parse_expr_call(&mut self, token: Token) -> MTree {
        let mut tree = MTree::new(token);
        self.expect(Token::PARENS_L);
        if ! self.peek(Token::PARENS_R) {
            tree.children.push(Rc::new(self.parse_expr()) );
            while self.accept(Token::COMMA) {
                tree.children.push(Rc::new(self.parse_expr()) );
            }
        }
        self.expect(Token::PARENS_R);
        return tree;
    }


    pub fn parse_expr_infix(&mut self, mut left: MTree, rbl: isize) -> MTree {
        loop {
            let op_infix = self.curr();
            if rbl > op_infix.binding_power().left {
                return left;
            }
            self.advance();
            let right = self.parse_expr_tok(op_infix.binding_power().right);
            left = MTree {
                token: op_infix,
                children: vec![
                    Rc::new(left),
                    Rc::new(right),
                ]
            }
        }
    }


}
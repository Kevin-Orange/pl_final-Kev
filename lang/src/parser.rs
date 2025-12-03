use crate::lexer::Lexer;
use crate::token::Token;
use crate::mtree::MTree;


const INDENT: usize = 2;

pub struct Parser {
    lexer: Lexer,
    pub indent: usize,
}

impl Parser {
    pub fn new(lexer: Lexer) -> Parser {
        Parser { lexer, indent: 0 }
    }

    pub fn analyze(&mut self) -> MTree {
        self.indent = 0;
        self.advance();
        let tree = self.parse();
        self.expect(Token::EOI);
        tree
    }
}

impl Parser {
    // utility functions for lexer
    pub fn curr(&mut self) -> Token {
        self.lexer.curr()
    }

    pub fn advance(&mut self) {
        self.lexer.advance();
    }

    pub fn peek(&mut self, symbol: Token) -> bool {
        self.lexer.curr() == symbol
    }

    pub fn expect(&mut self, symbol: Token) {
        if self.curr() == symbol {
            self.advance();
            println!("{:<indent$}expect({symbol:?})", "", indent = self.indent);
        } else {
            panic!("Expected '{symbol:?}', currently '{:?}'!", self.curr());
        }
    }

    pub fn expect_type(&mut self) {
        if self.curr().is_type() {
            self.advance();
            println!( "{:<indent$}expect({:?})", "", self.curr(), indent = self.indent);
        } else {
            panic!("Expected variable type, currently '{:?}'!", self.curr());
        }
    }

    pub fn accept(&mut self, symbol: Token) -> bool {
        if self.curr() == symbol {
            self.advance();
            true
        } else {
            false
        }
    }
}

impl Parser {
    // utility functions for pretty print

    pub fn indent_print(&mut self, msg: &'static str) {
        println!("{:<indent$}{:}", "", msg, indent = self.indent);
    }

    pub fn indent_increment(&mut self) {
        self.indent += INDENT;
    }
    pub fn indent_decrement(&mut self) {
        self.indent -= INDENT;
    }
}

impl Parser {
    // simple recursive descend parser

    pub fn parse(&mut self) -> MTree {
        let mut tree = MTree::new(Token::START);
        while !self.accept(Token::EOI) {
            tree._push(self.parse_func());
        }

        tree
    }

    pub fn parse_func(&mut self) -> MTree {
        self.indent_print("parse_func()");
        self.indent_increment();

        let mut child = MTree::new(Token::FUNC_DECL);

        {
            self.expect(Token::FUNC);

            let id = self.curr();
            self.expect(Token::id());
            child._push(MTree::new(id));

            child._push(self.parse_parameter_list());

            if self.accept(Token::ARROW_R) {
                let token = self.curr();
                self.expect_type();
                child._push(MTree::new(token));
            }

            child._push(self.parse_block_nest());
        }

        self.indent_decrement();

        child
    }

    pub fn parse_parameter_list(&mut self) -> MTree {
        self.indent_print("parse_parameter_list()");
        self.indent_increment();

        let mut child = MTree::new(Token::PARAM_LIST);

        {
            self.expect(Token::PARENS_L);
            if self.accept(Token::PARENS_R) {
                return child;
            }

            child._push(self.parse_parameter());
            while self.accept(Token::COMMA) {
                child._push(self.parse_parameter());
            }
            self.expect(Token::PARENS_R);
        }
        self.indent_decrement();

        child
    }

    pub fn parse_parameter(&mut self) -> MTree {
        self.indent_print("parse_parameter()");
        self.indent_increment();

        let mut child = MTree::new(Token::PARAM);

        {
            let id = self.curr();
            self.expect(Token::id());
            child._push(MTree::new(id));

            self.expect(Token::COLON);

            let type_token = self.curr();
            self.expect_type();
            child._push(MTree::new(type_token));
        }
        self.indent_decrement();

        child
    }

    pub fn parse_block_nest(&mut self) -> MTree {
        self.indent_print("parse_block_nest()");
        self.indent_increment();

        let mut child = MTree::new(Token::BLOCK);

        {
            self.expect(Token::BRACKET_L);
            while !self.peek(Token::BRACKET_R) {
                child._push(self.parse_statement());
            }
            self.expect(Token::BRACKET_R);
        }
        self.indent_decrement();

        child
    }
}

impl Parser {
    // statement/expression parsing functions

    pub fn parse_statement(&mut self) -> MTree {
        self.indent_print("parse_statement()");
        self.indent_increment();

        let child: MTree;
        {
            match self.curr() {
                Token::LET => child = self.parse_let(),
                Token::IF => child = self.parse_if(),
                Token::WHILE => child = self.parse_while(),
                Token::PRINT => child = self.parse_print(),  // <-- ADDED THIS LINE
                Token::RETURN => child = self.parse_return(),
                Token::BRACKET_L => child = self.parse_block_nest(),
                _ => {
                    child = self.parse_expr();
                    self.expect(Token::SEMICOLON);
                },
            }
        }
        self.indent_decrement();

        child
    }


    pub fn parse_let(&mut self) -> MTree {
        self.indent_print("parse_let()");
        self.indent_increment();

        let mut child = MTree::new(Token::LET_STMT);

        {
            self.expect(Token::LET);

            let id = self.curr();
            self.expect(Token::id());
            child._push(MTree::new(id));

            if self.accept(Token::COLON) {
                if self.curr().is_type() {
                    let type_token = self.curr();
                    self.advance();
                    child._push(MTree::new(type_token));
                } else {
                    panic!("Expected type token after ':', got {:?}", self.curr());
                }
            }

            if !self.peek(Token::SEMICOLON){
                self.expect(Token::ASSIGN);
                child._push(self.parse_expr());
            }
            
            self.expect(Token::SEMICOLON);
        }
        self.indent_decrement();

        child
    }

    pub fn parse_if(&mut self) -> MTree {
        self.indent_print("parse_if()");
        self.indent_increment();

        let mut child = MTree::new(Token::IF_STMT);

        {
            self.expect(Token::IF);
            child._push(self.parse_expr());
            child._push(self.parse_block_nest());
            if self.accept(Token::ELSE) {
                child._push(self.parse_block_nest());
            }
        }
        self.indent_decrement();

        child
    }

    pub fn parse_while(&mut self) -> MTree {
        self.indent_print("parse_while()");
        self.indent_increment();

        let mut child = MTree::new(Token::WHILE_STMT);

        {
            self.expect(Token::WHILE);
            child._push(self.parse_expr());
            child._push(self.parse_block_nest());
        }
        self.indent_decrement();

        child
    }

    pub fn parse_print(&mut self) -> MTree {
        self.indent_print("parse_print()");
        self.indent_increment();

        let mut child = MTree::new(Token::PRINT);

        {
            self.expect(Token::PRINT);
            child._push(self.parse_expr());
            self.expect(Token::SEMICOLON);
        }
        self.indent_decrement();

        child
    }

    pub fn parse_return(&mut self) -> MTree {
        self.indent_print("parse_return()");
        self.indent_increment();

        let mut child = MTree::new(Token::RTRN_STMT);
        {
            self.expect(Token::RETURN);
            child._push(self.parse_expr());
            self.expect(Token::SEMICOLON);
        }
        self.indent_decrement();

        child
    }
}

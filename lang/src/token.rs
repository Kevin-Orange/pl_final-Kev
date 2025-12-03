#![allow(warnings)]

use std::clone;
use std::mem::discriminant;
use strum_macros::EnumIter;

#[derive(Debug, Clone, EnumIter)]
pub enum Token {
    // Brackets
    PARENS_L,
    PARENS_R,

    BRACKET_L,
    BRACKET_R,

    BRACE_L,
    BRACE_R,

    // Separators
    POINT,
    COMMA,
    COLON,
    SEMICOLON,
    ARROW_R, // (->)

    // Arithmetic Operators
    ADD,
    SUB,
    MUL,
    DIV,

    // Relational Operators
    EQ,
    LT,
    GT,
    NEQ, // Not Equal (!=)
    NLT, // Not Less Than (>=)
    NGT, // Not Greater Than (<=)

    // Logical Operators
    NOT,
    AND,
    OR,

    // Assignment
    ASSIGN,

    // Keywords
    FUNC,
    LET,
    IF,
    ELSE,
    WHILE,
    PRINT,
    RETURN,

    // Identifiers
    ID { name: String },

    // Basic Types
    TYPE_INT32,
    TYPE_FLT32,
    TYPE_CHAR,
    TYPE_BOOL,

    // Literals
    LIT_INT32 { value: i32 },
    LIT_FLT32 { value: f32 },
    LIT_CHAR { value: char },
    LIT_BOOL { value: bool },
    LIT_STRING { value: String },

    ERROR,

    // End-of-Input
    EOI,

    // Metadata Nonterminals
    START,
    FUNC_DECL,
    PARAM_LIST,
    PARAM,
    BLOCK,
    IF_STMT,
    WHILE_STMT,
    LET_STMT,
    RTRN_STMT,
    EXPR,
}

impl PartialEq for Token {
    fn eq(&self, other: &Self) -> bool {
        discriminant(self) == discriminant(other)
    }
}

impl Token {
    pub fn id() -> Token {
        Token::ID {
            name: String::new(),
        }
    }

    pub fn lit_i32() -> Token {
        Token::LIT_INT32 { value: 0 }
    }

    pub fn lit_f32() -> Token {
        Token::LIT_FLT32 { value: 0.0 }
    }

    pub fn lit_char() -> Token {
        Token::LIT_CHAR { value: '\0' }
    }

    pub fn lit_bool() -> Token {
        Token::LIT_BOOL {
            value: false,
        }
    }

    pub fn lit_string() -> Token {
        Token::LIT_STRING { value: "".to_string() }
    }
}

impl Token {
    pub fn is_type(&self) -> bool {
        matches!(self, Token::TYPE_INT32 | Token::TYPE_FLT32 | Token::TYPE_CHAR | Token::TYPE_BOOL)
    }
}

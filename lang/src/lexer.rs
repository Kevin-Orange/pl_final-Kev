use crate::token::Token;

pub enum LexerState {
    Start,
    End,

    Chars,
    ReadChar,
    ReadString,
    Numbers,
    NumPoint,
    Decimals,

    Not,
    And,
    Or,

    Dash,
    Slash,
    Comment,

    Equal,
    Greater,
    Less,
}

pub struct Lexer {
    input_string: String,
    position: usize,
    state: LexerState,
    current_token: Token,
    buffer_string: String,
}

impl Lexer {
    pub fn new(input: String) -> Self {
        Lexer {
            input_string: input,
            position: 0,
            state: LexerState::Start,
            current_token: Token::EOI,
            buffer_string: String::new(),
        }
    }

    pub fn set_input(&mut self, input: String) {
        self.input_string = input;
        self.position = 0;
        self.state = LexerState::Start;
        self.current_token = Token::EOI;
        self.buffer_string = String::new();
    }

    pub fn advance(&mut self) -> Token {
        loop {
            if self.position == self.input_string.len() {
                match self.state {
                    LexerState::Greater => self.current_token = Token::GT,
                    LexerState::Less => self.current_token = Token::LT,
                    LexerState::Equal => self.current_token = Token::ASSIGN,
                    LexerState::Not => self.current_token = Token::NOT,
                    LexerState::Dash => self.current_token = Token::SUB,
                    LexerState::Slash => self.current_token = Token::DIV,
                    LexerState::And => self.current_token = Token::AND,
                    LexerState::Or => self.current_token = Token::OR,
                    LexerState::NumPoint => {
                        let value: i32 = self.buffer_string.parse().unwrap();
                        self.state = LexerState::Start;
                        self.current_token = Token::LIT_INT32 { value };
                        self.buffer_string = String::new();
                        self.position -= 1;
                        break;
                    }
                    _ => self.current_token = Token::EOI,
                }

                if !self.buffer_string.is_empty() {
                    self.state = LexerState::Start;
                    self.current_token = self.match_buffer_string();
                    self.buffer_string = String::new();
                    break;
                }
                self.state = LexerState::End;
                break;
            }

            let current_char = self.input_string.chars().nth(self.position).unwrap();
            self.position += 1;

            match self.state {
                LexerState::Start => match current_char {
                    'A'..='Z' | 'a'..='z' | '_' => {
                        self.state = LexerState::Chars;
                        self.buffer_string.push(current_char);
                    }
                    '0'..='9' => {
                        self.state = LexerState::Numbers;
                        self.buffer_string.push(current_char);
                    }
                    '\'' => {
                        self.state = LexerState::ReadChar;
                    }
                    '"' => {
                        self.state = LexerState::ReadString;
                    }
                    '{' => {
                        self.current_token = Token::BRACE_L;
                        break;
                    }
                    '}' => {
                        self.current_token = Token::BRACE_R;
                        break;
                    }
                    '[' => {
                        self.current_token = Token::BRACKET_L;
                        break;
                    }
                    ']' => {
                        self.current_token = Token::BRACKET_R;
                        break;
                    }
                    '(' => {
                        self.current_token = Token::PARENS_L;
                        break;
                    }
                    ')' => {
                        self.current_token = Token::PARENS_R;
                        break;
                    }
                    '!' => {
                        self.state = LexerState::Not;
                    }
                    '&' => {
                        self.state = LexerState::And;
                    }
                    '|' => {
                        self.state = LexerState::Or;
                    }
                    '.' => {
                        self.current_token = Token::POINT;
                        break;
                    }
                    ',' => {
                        self.current_token = Token::COMMA;
                        break;
                    }
                    ':' => {
                        self.current_token = Token::COLON;
                        break;
                    }
                    ';' => {
                        self.current_token = Token::SEMICOLON;
                        break;
                    }
                    '+' => {
                        self.current_token = Token::ADD;
                        break;
                    }
                    '-' => {
                        self.state = LexerState::Dash;
                    }
                    '*' => {
                        self.current_token = Token::MUL;
                        break;
                    }
                    '/' => {
                        self.state = LexerState::Slash;
                    }
                    '=' => {
                        self.state = LexerState::Equal;
                    }
                    '<' => {
                        self.state = LexerState::Less;
                    }
                    '>' => {
                        self.state = LexerState::Greater;
                    }

                    _ => {}
                },

                LexerState::Chars => match current_char {
                    'A'..='Z' | '_' | 'a'..='z' | '-' | '0'..='9' => {
                        self.buffer_string.push(current_char);
                    }

                    _ => {
                        self.state = LexerState::Start;
                        self.current_token = self.match_buffer_string();
                        self.buffer_string = String::new();

                        self.position -= 1;
                        break;
                    }
                },
                LexerState::Numbers => match current_char {
                    '0'..='9' => {
                        self.buffer_string.push(current_char);
                    }

                    '.' => {
                        self.state = LexerState::NumPoint;
                    }

                    _ => {
                        self.state = LexerState::Start;
                        let value: i32 = self.buffer_string.parse().unwrap();
                        self.current_token = Token::LIT_INT32 { value };
                        self.buffer_string = String::new();

                        self.position -= 1;
                        break;
                    }
                },
                LexerState::NumPoint => match current_char {
                    '0'..='9' => {
                        self.state = LexerState::Decimals;
                        self.buffer_string.push('.');
                        self.buffer_string.push(current_char);
                    }

                    _ => {
                        self.state = LexerState::Start;
                        let value: i32 = self.buffer_string.parse().unwrap();
                        self.current_token = Token::LIT_INT32 { value };
                        self.buffer_string = String::new();

                        self.position -= 2;
                        break;
                    }
                },
                LexerState::Decimals => match current_char {
                    '0'..='9' => {
                        self.buffer_string.push(current_char);
                    }

                    _ => {
                        self.state = LexerState::Start;
                        let value: f32 = self.buffer_string.parse().unwrap();
                        self.current_token = Token::LIT_FLT32 { value };
                        self.buffer_string = String::new();

                        self.position -= 1;
                        break;
                    }
                },
                LexerState::ReadChar => match current_char {
                    '\'' => {
                        self.state = LexerState::Start;
                        if self.buffer_string.len() == 1 {
                            let value = self.buffer_string.chars().nth(0).unwrap();
                            self.current_token = Token::LIT_CHAR { value };
                            self.buffer_string = String::new();
                            break;
                        }
                        self.buffer_string = String::new();
                    }
                    _ => {
                        self.buffer_string.push(current_char);
                    }
                },
                LexerState::ReadString => match current_char {
                    '"' => {
                        self.state = LexerState::Start;
                        let value = self.buffer_string.clone();
                        self.current_token = Token::LIT_STRING { value };
                        self.buffer_string = String::new();
                        break;
                    }
                    _ => {
                        self.buffer_string.push(current_char);
                    }
                },

                LexerState::Not => match current_char {
                    '=' => {
                        self.state = LexerState::Start;
                        self.current_token = Token::NEQ;
                        break;
                    }
                    _ => {
                        self.state = LexerState::Start;
                        self.current_token = Token::NOT;
                        self.position -= 1;
                        break;
                    }
                },
                LexerState::And => match current_char {
                    '&' => {
                        self.state = LexerState::Start;
                        self.current_token = Token::AND;
                        break;
                    }
                    _ => {
                        self.state = LexerState::Start;
                        self.position -= 1;
                    }
                },
                LexerState::Or => match current_char {
                    '|' => {
                        self.state = LexerState::Start;
                        self.current_token = Token::OR;
                        break;
                    }
                    _ => {
                        self.state = LexerState::Start;
                        self.position -= 1;
                    }
                },
                LexerState::Dash => match current_char {
                    '>' => {
                        self.state = LexerState::Start;
                        self.current_token = Token::ARROW_R;
                        break;
                    }
                    _ => {
                        self.state = LexerState::Start;
                        self.current_token = Token::SUB;
                        self.position -= 1;
                        break;
                    }
                },
                LexerState::Equal => match current_char {
                    '=' => {
                        self.state = LexerState::Start;
                        self.current_token = Token::EQ;
                        break;
                    }
                    _ => {
                        self.state = LexerState::Start;
                        self.current_token = Token::ASSIGN;
                        self.position -= 1;
                        break;
                    }
                },
                LexerState::Greater => match current_char {
                    '=' => {
                        self.state = LexerState::Start;
                        self.current_token = Token::NLT;
                        break;
                    }
                    _ => {
                        self.state = LexerState::Start;
                        self.current_token = Token::GT;
                        self.position -= 1;
                        break;
                    }
                },
                LexerState::Less => match current_char {
                    '=' => {
                        self.state = LexerState::Start;
                        self.current_token = Token::NGT;
                        break;
                    }
                    _ => {
                        self.state = LexerState::Start;
                        self.current_token = Token::LT;
                        self.position -= 1;
                        break;
                    }
                },
                LexerState::Slash => match current_char {
                    '/' => {
                        // Comments - skip until end of line
                        self.state = LexerState::Comment;
                    }

                    _ => {
                        self.state = LexerState::Start;
                        self.current_token = Token::DIV;
                        self.position -= 1;
                        break;
                    }
                },
                LexerState::Comment => match current_char {
                    '\n' | '\r' => {
                        // End of comment, return to start
                        self.state = LexerState::Start;
                    }
                    _ => {
                        // Continue skipping comment characters
                    }
                },

                _ => {}
            }
        }
        self.curr()
    }

    pub fn curr(&self) -> Token {
        self.current_token.clone()
    }

    pub fn print_tokens(&mut self) {
        println!("");
        loop {
            self.advance();
            if let Token::EOI = self.curr() {
                break;
            }
            print!("{:?}, ", self.curr());
        }
        print!("{:?}", self.curr());
    }

    fn match_buffer_string(&mut self) -> Token {
        let string = self.buffer_string.as_str();
        match self.buffer_string.as_str() {
            "func" => Token::FUNC,
            "let" => Token::LET,
            "if" => Token::IF,
            "else" => Token::ELSE,
            "return" => Token::RETURN,
            "while" => Token::WHILE,
            "print" => Token::PRINT,
            "i32" => Token::TYPE_INT32,
            "f32" => Token::TYPE_FLT32,
            "char" => Token::TYPE_CHAR,
            "bool" => Token::TYPE_BOOL,
            "true" => Token::LIT_BOOL { value: true },
            "false" => Token::LIT_BOOL { value: false },
            _ => {
                if string.contains('.') {
                    let value = string.parse::<f32>().unwrap();
                    if value.fract() != 0.0 {
                        return Token::LIT_FLT32 { value };
                    } else {
                        return Token::LIT_INT32 {
                            value: value as i32,
                        };
                    }
                }
                if let Ok(value) = string.parse::<i32>() {
                    return Token::LIT_INT32 { value };
                }

                return Token::ID {
                    name: string.to_string(),
                };
            }
        }
    }
}

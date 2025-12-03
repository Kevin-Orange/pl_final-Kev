use std::collections::HashMap;

use crate::token::Token;
use crate::mtree::MTree as ParseTree; // parse-tree type

#[derive(Debug, Clone, PartialEq)]
pub enum Type {
    Int,
    Bool,
    Unknown,
}

#[derive(Debug)]
pub struct SymbolTable {
    vars: HashMap<String, Type>,
}

impl SymbolTable {
    pub fn new() -> Self {
        Self {
            vars: HashMap::new(),
        }
    }

    pub fn declare(&mut self, name: &str, ty: Type) -> Result<(), String> {
        if self.vars.contains_key(name) {
            Err(format!("Variable '{}' already declared", name))
        } else {
            self.vars.insert(name.to_string(), ty);
            Ok(())
        }
    }

    pub fn check(&self, name: &str) -> Result<Type, String> {
        self.vars
            .get(name)
            .cloned()
            .ok_or_else(|| format!("Variable '{}' not declared", name))
    }
}

/// Semantic AST used by analyzer.
#[derive(Debug)]
pub enum MTree {
    START { funcs: Vec<MTree> },
    FUNC_DECL { name: String, params: Vec<(String, Type)>, ret_type: Type, body: Box<MTree> },
    BLOCK { stmts: Vec<MTree> },
    LET_STMT { id: String, ty: Type, expr: Option<Box<MTree>> },
    ASSIGN { id: String, expr: Box<MTree> },
    RTRN_STMT { expr: Box<MTree> },
    WHILE_STMT { cond: Box<MTree>, body: Box<MTree> },
    IF_STMT { cond: Box<MTree>, then_block: Box<MTree>, else_block: Option<Box<MTree>> },
    PRINT_STMT { expr: Box<MTree> },
    EXPR { left: Box<MTree>, op: String, right: Box<MTree> },
    CALL { name: String, args: Vec<MTree> },
    ID { name: String },
    LIT_INT { value: i32 },
    LIT_BOOL { value: bool },
}

impl MTree {
    // small helper constructors
    pub fn lit_int(i: i32) -> Self { MTree::LIT_INT { value: i } }
    pub fn lit_bool(b: bool) -> Self { MTree::LIT_BOOL { value: b } }
    pub fn id(name: String) -> Self { MTree::ID { name } }
}

/// Convert parse-tree
pub fn from_parse_tree(pt: &ParseTree) -> Result<MTree, String> {
    match &pt.token {
        // program root: children are FUNC_DECL nodes
        Token::START => {
            let mut funcs = Vec::new();
            for c in &pt.children {
                let child = from_parse_tree(c)?;
                funcs.push(child);
            }
            Ok(MTree::START { funcs })
        }

        // function declaration node: expected children:
        // [ ID(name), PARAM_LIST, (optional return type token), BLOCK ]
        Token::FUNC_DECL => {
            let mut iter = pt.children.iter();
            // name
            let name_node = iter.next().ok_or("Missing function name")?;
            let name = match &name_node.token {
                Token::ID { name } => name.clone(),
                _ => return Err("Expected ID in FUNC_DECL".into()),
            };

            // params
            let params_node = iter.next().ok_or("Missing param list")?;
            let mut params: Vec<(String, Type)> = Vec::new();
            // PARAM_LIST children are PARAM nodes
            for p in &params_node.children {
                // param node: [ ID, TYPE ]
                let id_node = p.children.get(0).ok_or("Param missing id")?;
                let type_node = p.children.get(1).ok_or("Param missing type")?;
                let pname = match &id_node.token {
                    Token::ID { name } => name.clone(),
                    _ => return Err("Expected ID in param".into()),
                };
                let ptype = match &type_node.token {
                    Token::TYPE_INT32 => Type::Int,
                    Token::TYPE_BOOL => Type::Bool,
                    _ => Type::Unknown,
                };
                params.push((pname, ptype));
            }

            // next child:
            let mut ret_type = Type::Unknown;
            let mut block_node_opt = None;
            if let Some(next) = iter.next() {
                match &next.token {
                    Token::TYPE_INT32 => {
                        ret_type = Type::Int;
                        block_node_opt = iter.next();
                    }
                    Token::TYPE_BOOL => {
                        ret_type = Type::Bool;
                        block_node_opt = iter.next();
                    }
                    Token::BRACKET_L | Token::BLOCK => {
                        // next is block node
                        block_node_opt = Some(next);
                    }
                    _ => {
                        // fallback: try next child a block maybe
                        block_node_opt = Some(next);
                    }
                }
            }
            let block_node = block_node_opt.ok_or("Missing function block")?;
            let body = from_parse_tree(block_node)?;
            Ok(MTree::FUNC_DECL {
                name,
                params,
                ret_type,
                body: Box::new(body),
            })
        }

        // block: children are statements
        Token::BLOCK => {
            let mut stmts = Vec::new();
            for c in &pt.children {
                let stmt = from_parse_tree(c)?;
                stmts.push(stmt);
            }
            Ok(MTree::BLOCK { stmts })
        }

        
        // [ ID, optional TYPE, optional expr ]
        Token::LET_STMT => {
            let id_node = pt.children.get(0).ok_or("let missing id")?;
            let id = match &id_node.token {
                Token::ID { name } => name.clone(),
                _ => return Err("Expected id in let".into()),
            };

            
            let mut ty = Type::Unknown;
            let mut expr: Option<Box<MTree>> = None;

            if pt.children.len() >= 2 {
                let second = &pt.children[1];
                match &second.token {
                    Token::TYPE_INT32 => {
                        ty = Type::Int;
                        if pt.children.len() >= 3 {
                            let expr_node = &pt.children[2];
                            expr = Some(Box::new(from_parse_tree(expr_node)?));
                        }
                    }
                    Token::TYPE_BOOL => {
                        ty = Type::Bool;
                        if pt.children.len() >= 3 {
                            let expr_node = &pt.children[2];
                            expr = Some(Box::new(from_parse_tree(expr_node)?));
                        }
                    }
                    Token::ASSIGN | Token::LIT_INT32 { .. } | Token::PARENS_L | Token::ID { .. } => {
                        // no type, second is expression
                        expr = Some(Box::new(from_parse_tree(second)?));
                    }
                    _ => {
                        
                    }
                }
            }

            Ok(MTree::LET_STMT { id, ty, expr })
        }

        // (token = Token::ASSIGN)
        Token::ASSIGN => {
            // children: left (ID) and right (expr)
            if pt.children.len() != 2 {
                return Err("Assign must have two children".into());
            }
            let left = &pt.children[0];
            let id = match &left.token {
                Token::ID { name } => name.clone(),
                _ => return Err("Left side of assign must be ID".into()),
            };
            let right = from_parse_tree(&pt.children[1])?;
            Ok(MTree::ASSIGN { id, expr: Box::new(right) })
        }

        // return statement: first child is expression
        Token::RTRN_STMT => {
            let expr_node = pt.children.get(0).ok_or("return missing expr")?;
            let e = from_parse_tree(expr_node)?;
            Ok(MTree::RTRN_STMT { expr: Box::new(e) })
        }

        // while statement: condition and body
        Token::WHILE_STMT => {
            let cond_node = pt.children.get(0).ok_or("while missing condition")?;
            let body_node = pt.children.get(1).ok_or("while missing body")?;
            let cond = from_parse_tree(cond_node)?;
            let body = from_parse_tree(body_node)?;
            Ok(MTree::WHILE_STMT { 
                cond: Box::new(cond), 
                body: Box::new(body) 
            })
        }

        // if 
        Token::IF_STMT => {
            let cond_node = pt.children.get(0).ok_or("if missing condition")?;
            let then_node = pt.children.get(1).ok_or("if missing then block")?;
            let cond = from_parse_tree(cond_node)?;
            let then_block = from_parse_tree(then_node)?;
            
            let else_block = if pt.children.len() > 2 {
                Some(Box::new(from_parse_tree(&pt.children[2])?))
            } else {
                None
            };
            
            Ok(MTree::IF_STMT { 
                cond: Box::new(cond), 
                then_block: Box::new(then_block),
                else_block
            })
        }

        // print 
        Token::PRINT => {
            let expr_node = pt.children.get(0).ok_or("print missing expr")?;
            let e = from_parse_tree(expr_node)?;
            Ok(MTree::PRINT_STMT { expr: Box::new(e) })
        }

        // Unary operators 
        Token::NOT => {
            if pt.children.len() != 1 {
                return Err("unary NOT must have one child".into());
            }
            let child = from_parse_tree(&pt.children[0])?;
            // Represent unary NOT as a special expression with only right operand
            Ok(MTree::EXPR { 
                left: Box::new(MTree::LIT_BOOL { value: false }), // dummy
                op: "!".to_string(), 
                right: Box::new(child) 
            })
        }

        // expression nodes (binary ops)
        Token::ADD | Token::SUB | Token::MUL | Token::DIV
        | Token::EQ | Token::NEQ | Token::LT | Token::GT | Token::NLT | Token::NGT
        | Token::AND | Token::OR => {
            // Could be unary or binary
            if pt.children.len() == 1 {
                // Unary minus
                let child = from_parse_tree(&pt.children[0])?;
                let op = match &pt.token {
                    Token::SUB => "-",
                    _ => return Err("Only SUB can be unary in this position".into()),
                };
                Ok(MTree::EXPR { 
                    left: Box::new(MTree::LIT_INT { value: 0 }), // dummy
                    op: format!("unary{}", op), 
                    right: Box::new(child) 
                })
            } else if pt.children.len() == 2 {
                let l = from_parse_tree(&pt.children[0])?;
                let r = from_parse_tree(&pt.children[1])?;
                let op = match &pt.token {
                    Token::ADD => "+",
                    Token::SUB => "-",
                    Token::MUL => "*",
                    Token::DIV => "/",
                    Token::EQ => "==",
                    Token::NEQ => "!=",
                    Token::LT => "<",
                    Token::GT => ">",
                    Token::NLT => ">=",
                    Token::NGT => "<=",
                    Token::AND => "&&",
                    Token::OR => "||",
                    _ => "?",
                };
                Ok(MTree::EXPR { left: Box::new(l), op: op.to_string(), right: Box::new(r) })
            } else {
                return Err("operator must have one or two children".into());
            }
        }

        // parentheses wrap
        Token::PARENS_L => {
            
            if pt.children.len() >= 1 {
                from_parse_tree(&pt.children[0])
            } else {
                Err("empty parens".into())
            }
        }

        // identifiers - could be variable or function call
        Token::ID { name } => {
            
            if pt.children.len() > 0 {
                
                let mut args = Vec::new();
                for arg_node in &pt.children {
                    args.push(from_parse_tree(arg_node)?);
                }
                Ok(MTree::CALL { name: name.clone(), args })
            } else {
                
                Ok(MTree::ID { name: name.clone() })
            }
        }

        Token::LIT_INT32 { value } => Ok(MTree::LIT_INT { value: *value }),
        Token::LIT_BOOL { value } => Ok(MTree::LIT_BOOL { value: *value }),

        // unexpected / unhandled tokens
        other => Err(format!("Unhandled token in converter: {:?}", other)),
    }
}

/// Semantic analyzer
pub fn analyze(tree: &MTree, symbols: &mut SymbolTable) -> Result<Type, Vec<String>> {
    let mut errors: Vec<String> = Vec::new();

    fn helper(node: &MTree, symbols: &mut SymbolTable, errors: &mut Vec<String>) -> Type {
        match node {
            MTree::START { funcs } => {
                for f in funcs {
                    helper(f, symbols, errors);
                }
                Type::Unknown
            }
            MTree::FUNC_DECL { name, params, ret_type, body } => {
                // new local symbol table per function -- do not mutate outer symbols
                let mut local = SymbolTable::new();
                for (pname, ptype) in params {
                    let _ = local.declare(pname, ptype.clone());
                }
                let body_type = helper(body, &mut local, errors);
                
                // Check return type matches (if specified)
                if *ret_type != Type::Unknown && body_type != *ret_type && body_type != Type::Unknown {
                    errors.push(format!(
                        "Function '{}' declared return type {:?}, but body returns {:?}",
                        name, ret_type, body_type
                    ));
                }
                Type::Unknown
            }
            MTree::BLOCK { stmts } => {
                let mut last_type = Type::Unknown;
                for s in stmts {
                    last_type = helper(s, symbols, errors);
                }
                last_type
            }
            MTree::LET_STMT { id, ty, expr } => {
                let inferred_ty = if let Some(expr_node) = expr {
                    let et = helper(expr_node, symbols, errors);
                    if *ty != Type::Unknown && et != *ty && et != Type::Unknown {
                        errors.push(format!("Type mismatch for '{}': expected {:?}, found {:?}", id, ty, et));
                    }
                    
                    if *ty == Type::Unknown { et } else { ty.clone() }
                } else {
                    ty.clone()
                };
                
                
                let _ = symbols.declare(id, inferred_ty).map_err(|e| errors.push(e)).ok();
                Type::Unknown
            }
            MTree::ASSIGN { id, expr } => {
                match symbols.check(id) {
                    Ok(var_type) => {
                        let expr_type = helper(expr, symbols, errors);
                        if var_type != expr_type && expr_type != Type::Unknown && var_type != Type::Unknown {
                            errors.push(format!("Assignment type mismatch for '{}': {:?} vs {:?}", id, var_type, expr_type));
                        }
                    }
                    Err(e) => errors.push(e),
                }
                Type::Unknown
            }
            MTree::RTRN_STMT { expr } => helper(expr, symbols, errors),
            MTree::WHILE_STMT { cond, body } => {
                // Check condition type
                let cond_type = helper(cond, symbols, errors);
                if cond_type != Type::Bool && cond_type != Type::Unknown {
                    errors.push(format!("While condition must be Bool, found {:?}", cond_type));
                }
                // Analyze body
                helper(body, symbols, errors);
                Type::Unknown
            }
            MTree::IF_STMT { cond, then_block, else_block } => {
                // Check condition type
                let cond_type = helper(cond, symbols, errors);
                if cond_type != Type::Bool && cond_type != Type::Unknown {
                    errors.push(format!("If condition must be Bool, found {:?}", cond_type));
                }
                // Analyze then block
                let then_type = helper(then_block, symbols, errors);
                // Analyze else block if present
                let else_type = if let Some(else_blk) = else_block {
                    helper(else_blk, symbols, errors)
                } else {
                    Type::Unknown
                };
                
                if then_type != Type::Unknown && else_type != Type::Unknown && then_type != else_type {
                    errors.push(format!("If branches return different types: {:?} vs {:?}", then_type, else_type));
                }
                // Return the type if both branches agree
                if then_type != Type::Unknown { then_type } else { else_type }
            }
            MTree::PRINT_STMT { expr } => {
                // Print can take any type, just check the expression is valid
                helper(expr, symbols, errors);
                Type::Unknown
            }
            MTree::EXPR { left, op, right } => {
                let rt = helper(right, symbols, errors);
                
                // Handle unary operators
                if op == "!" {
                    if rt != Type::Bool && rt != Type::Unknown {
                        errors.push(format!("Unary NOT requires Bool type, found {:?}", rt));
                    }
                    return Type::Bool;
                }
                if op == "unary-" {
                    if rt != Type::Int && rt != Type::Unknown {
                        errors.push(format!("Unary minus requires Int type, found {:?}", rt));
                    }
                    return Type::Int;
                }
                
                // Binary operators
                let lt = helper(left, symbols, errors);
                match op.as_str() {
                    "+"|"-"|"*"|"/" => {
                        
                        if (lt != Type::Int && lt != Type::Unknown) || (rt != Type::Int && rt != Type::Unknown) {
                            errors.push(format!("Arithmetic op '{}' requires Int types, found {:?} and {:?}", op, lt, rt));
                        }
                        Type::Int
                    }
                    "=="|"!=" => {
                        if lt != rt && lt != Type::Unknown && rt != Type::Unknown {
                            errors.push(format!("Comparison '{}' requires matching types, found {:?} and {:?}", op, lt, rt));
                        }
                        Type::Bool
                    }
                    "<"|">"|">="|"<=" => {
                        
                        if (lt != Type::Int && lt != Type::Unknown) || (rt != Type::Int && rt != Type::Unknown) {
                            errors.push(format!("Relational op '{}' requires Int types, found {:?} and {:?}", op, lt, rt));
                        }
                        Type::Bool
                    }
                    "&&"|"||" => {
                        if (lt != Type::Bool && lt != Type::Unknown) || (rt != Type::Bool && rt != Type::Unknown) {
                            errors.push(format!("Logical op '{}' requires Bool types, found {:?} and {:?}", op, lt, rt));
                        }
                        Type::Bool
                    }
                    _ => Type::Unknown,
                }
            }
            MTree::CALL { name: _, args } => {
                
                for arg in args {
                    helper(arg, symbols, errors);
                }
                // Assume function returns Unknown since no track function signatures
                Type::Unknown
            }
            MTree::ID { name } => {
                match symbols.check(name) {
                    Ok(ty) => ty,
                    Err(e) => {
                        errors.push(e);
                        Type::Unknown
                    }
                }
            }
            MTree::LIT_INT { .. } => Type::Int,
            MTree::LIT_BOOL { .. } => Type::Bool,
        }
    }

    let ty = helper(tree, symbols, &mut errors);
    if errors.is_empty() { Ok(ty) } else { Err(errors) }
}




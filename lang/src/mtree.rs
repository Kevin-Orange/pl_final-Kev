use crate::token::Token;
use std::rc::Rc;

#[derive(Debug)]
pub struct MTree {
    pub token: Token,
    pub children: Vec<Rc<MTree>>,
}

impl MTree {
    pub fn new(token: Token) -> MTree {
        MTree {
            token,
            children: vec![],
        }
    }

    pub fn _push(&mut self, tree: MTree) {
        self.children.push(Rc::new(tree));
    }

    pub fn node_string(&self) -> String {
        format!("{:?}", self.token)
    }

    fn print_recursively(&self, level: usize) {
        let shift = 2 * level;
        print!("{:1$}", "", shift);
        println!("{}", self.node_string());
        for child in &self.children {
            child.as_ref().print_recursively(level + 1);
        }
    }

    pub fn print(&self) {
        self.print_recursively(0);
    }
}


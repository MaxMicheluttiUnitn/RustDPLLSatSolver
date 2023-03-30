use std::cell::RefCell;
use std::rc::Rc;
use std::collections::HashSet;

use crate::sat::{Literal, CNF, Clause};

#[derive(Debug)]
pub struct BooleanFormula{
    root: Formula,
    variables: HashSet<i32>,
}

#[derive(Debug)]
struct Formula{
    root: Node
}

type Link=Rc<RefCell<Formula>>;

#[derive(Debug,Clone)]
enum Node{
    Variable(i32),
    Or(Vec<Link>), 
    And(Vec<Link>),
    Xor(Link,Link),
    Not(Link),
    Iff(Link,Link),
    Implies(Link,Link),
    IsImpliedBy(Link,Link),
    Exists(i32,Link),
    ForEach(i32,Link),
    True,
    False
}

impl BooleanFormula{
    pub fn new_default()->Self{
        let formula=Formula::new_default();
        Self::from_formula(formula)
    }

    pub fn to_string(&self)->String{
        self.root.to_string()
    }

    pub fn make_nnf(&mut self){
        self.root.make_nnf();
        self.update();
    }

    pub fn make_cnf_label(&mut self){
        self.root.make_cnf_label();
        self.update();
    }

    pub fn get_variables(&self)->&HashSet<i32>{
        return &self.variables
    }

    pub fn not(&self)->Self{
        let root_neg=self.root.clone();
        let res =Formula::new(Node::Not(Rc::new(RefCell::new(root_neg))));
        Self::from_formula(res)
    }

    pub fn update(&mut self){
        self.variables=self.root.find_variables();       
    }

    pub fn entail(&self, formula: &BooleanFormula)->Self{
        let self_cloned=Rc::new(RefCell::new(self.root.clone()));
        let formula_cloned=Rc::new(RefCell::new(formula.root.clone()));
        let result=Formula::new(Node::Implies(self_cloned,formula_cloned));
        Self::from_formula(result)
    }

    pub fn from_string(input:String)->Result<Self,String>{
        let formula=match Formula::from_string(input.clone()){
            Ok(f)=>f,
            Err(s)=>{return Err(s);}
        };
        Ok(Self::from_formula(formula))
    }

    pub fn from_str(input:&str)->Result<Self,String>{
        Self::from_string(input.to_string())
    }

    fn from_formula(formula:Formula)->Self{
        let variables=HashSet::new();
        let mut res=BooleanFormula { 
            root: formula,
            variables,
        };
        res.update();
        res
    }

    pub fn is_cnf(&self)->bool{
        self.root.is_cnf()
    }

    pub fn to_cnf_representation(&self)->CNF{
        self.root.to_cnf_representation()
    }

    pub fn get_nnf(&self)->Self{
        let mut cloned=self.clone();
        cloned.make_nnf();
        cloned
    }

    pub fn get_cnf(&self)->Self{
        let mut cloned=self.clone();
        cloned.make_cnf_label();
        cloned
    }

    pub fn is_true(&self)->bool{
        if self.is_cnf(){
            self.root.is_true()
        }else{
            self.get_cnf().is_true()
        }
    }

    pub fn is_false(&self)->bool{
        if self.is_cnf(){
            self.root.is_false()
        }else{
            self.get_cnf().is_false()
        }
    }

    pub fn remove_quantifiers(&mut self){
        self.root.remove_quantifiers();
        self.root.simplify_truth();
        self.variables=self.root.find_variables();
        self.update();
    }

    pub fn without_quantifiers(&self) -> Self{
        let mut cloned=self.clone();
        cloned.remove_quantifiers();
        cloned
    }
}

impl Clone for BooleanFormula{
    fn clone(&self) -> Self{
        let mut res=BooleanFormula { root: self.root.clone(), variables: HashSet::new() };
        res.update();
        res
    }
}

impl Formula{
    pub fn new(node:Node) -> Self{
        Formula{
            root: node
        }
    }

    pub fn new_default() -> Self{
        Formula{
            root: Node::Variable(0)
        }
    }

    pub fn from_string(s:String) -> Result<Self,String>{
        let mut open="(".to_string();
        open.push_str(&s);
        open.push_str(")");
        let vec=open.chars().collect();
        let mut index: usize=0;
        match Self::from_string_at_char(&vec,&mut index){
            Ok(node)=>{
                if index==open.len(){
                    let res=Formula::new(node);
                    Ok(res)
                }else{
                    let res=Formula::new(node);
                    let str=format!("Formula not well formatted: found extra characters at the end of parsed formula \"{}\"",res.to_string());
                    Err(str.to_string())
                }
            },
            Err(s)=>{
                println!("{} on {}",index, open.len());
                Err(s)
            }
        }
    }

    fn from_string_at_char(string: &Vec<char>, index: &mut usize) -> Result<Node,String>{
        if *string.get(*index).unwrap()!='(' {
            let error=format!("Formula not well formatted: missing opening brackets!
                At position {} of {}
                Expected \"(\"
                Found \"{}\" instead",*index,string.into_iter().collect::<String>(),*string.get(*index).unwrap());
            return Err(error);
        }
        let left_formula=match Self::read_atom(string,index){
            Ok(node)=>node,
            Err(s)=>{return Err(s);}
        };
        if *index>=string.len(){
            return Err("Formula not well formatted: opened brackets need to be closed or filled with opeartors!".to_string());
        }   
        while *string.get(*index).unwrap()==' '{
            *index+=1;
            if *index>=string.len(){
                return Err("Formula not well formatted: opened brackets need to be closed or filled with opeartors!".to_string());
            }    
        }
        let formula= match *string.get(*index).unwrap(){
            ')'=>{
                *index+=1;
                return Ok(left_formula);
            },
            '+'=>{ // and
                let mut atom_vec:Vec<Link>=vec![];
                atom_vec.push(Rc::new(RefCell::new(Formula::new(left_formula))));
                loop{
                    let next_atom=match Self::read_atom(string, index){
                        Ok(node)=>node,
                        Err(s)=>{return Err(s);}
                    };
                    atom_vec.push(Rc::new(RefCell::new(Formula::new(next_atom))));
                    while *string.get(*index).unwrap()==' '{
                        *index+=1;
                        if *index>=string.len(){
                            return Err("Formula not well formatted: and operator needs to be closed or continued!".to_string());
                        }    
                    }
                    if *string.get(*index).unwrap()=='+'{
                        continue;
                    }
                    if *string.get(*index).unwrap()==')'{
                        break;
                    }
                    let error=format!("Formula not well formatted: Invalid character in sequence of and operators!
                        At position {} of {}
                        Expected \")\" or \"+\"
                        Found \"{}\" instead",*index,string.into_iter().collect::<String>(),*string.get(*index).unwrap());
                    return Err(error);
                }
                Node::And(atom_vec)
            },
            '*'=>{ // or
                let mut atom_vec:Vec<Link>=vec![];
                atom_vec.push(Rc::new(RefCell::new(Formula::new(left_formula))));
                loop{
                    let next_atom=match Self::read_atom(string, index){
                        Ok(node)=>node,
                        Err(s)=>{return Err(s);}
                    };
                    atom_vec.push(Rc::new(RefCell::new(Formula::new(next_atom))));
                    while *string.get(*index).unwrap()==' '{
                        *index+=1;
                        if *index>=string.len(){
                            return Err("Formula not well formatted: or operator needs to be closed or continued!".to_string());
                        }    
                    }
                    if *string.get(*index).unwrap()=='*'{
                        continue;
                    }
                    if *string.get(*index).unwrap()==')'{
                        break;
                    }
                    let error=format!("Formula not well formatted: Invalid character in sequence of or operators!
                        At position {} of {}
                        Expected \")\" or \"*\"
                        Found \"{}\" instead",*index,string.into_iter().collect::<String>(),*string.get(*index).unwrap());
                    return Err(error);
                }
                Node::Or(atom_vec)
            },
            '%'=>{ // xor
                let right_formula=match Self::read_atom(string, index){
                    Ok(node)=>node,
                    Err(s)=>{return Err(s);}
                };
                Node::Xor(
                    Rc::new(RefCell::new(Formula::new(left_formula))), 
                    Rc::new(RefCell::new(Formula::new(right_formula))))
            },
            '<'=>{ // left impl
                let right_formula=match Self::read_atom(string, index){
                    Ok(node)=>node,
                    Err(s)=>{return Err(s);}
                };
                Node::IsImpliedBy(
                    Rc::new(RefCell::new(Formula::new(left_formula))), 
                    Rc::new(RefCell::new(Formula::new(right_formula))))
            },
            '>'=>{ // impl
                let right_formula=match Self::read_atom(string, index){
                    Ok(node)=>node,
                    Err(s)=>{return Err(s);}
                };
                Node::Implies(
                    Rc::new(RefCell::new(Formula::new(left_formula))), 
                    Rc::new(RefCell::new(Formula::new(right_formula))))
            },
            '='=>{ // iff
                let right_formula=match Self::read_atom(string, index){
                    Ok(node)=>node,
                    Err(s)=>{return Err(s);}
                };
                Node::Iff(
                    Rc::new(RefCell::new(Formula::new(left_formula))), 
                    Rc::new(RefCell::new(Formula::new(right_formula))))
            },
            _=>{
                let error=format!("Formula not well formatted: invalid operator found!
                    At position {} of {}
                    Expected \"+\" (and) or \"*\" (or) or \">\" (impl) or \"<\" (left impl) or \"=\" (iff) or \"%\" (xor)
                    Found \"{}\" instead",*index,string.into_iter().collect::<String>(),*string.get(*index).unwrap());
                return Err(error);
            }
        };
        while *string.get(*index).unwrap()==' '{
            *index+=1;
            if *index>=string.len(){
                return Err("Formula not well formatted: missing closed brackets".to_string());
            }    
        }
        if *string.get(*index).unwrap()!=')'{
            let error=format!("Formula not well formatted: brackets must be closed before starting a new subformula!
                At position {} of {}
                Expected \")\"
                Found \"{}\" instead",*index,string.into_iter().collect::<String>(),*string.get(*index).unwrap());
            return Err(error);
        }
        *index+=1;
        return Ok(formula);

    }

    fn read_variable_name(string: &Vec<char>, index: &mut usize)->Result<i32,String>{
        while *string.get(*index).unwrap()==' '{
            *index+=1;
            if *index>=string.len(){
                return Err("Formula not well formatted: Found no character while trying to read a variable!".to_string());
            }
        }
        match *string.get(*index).unwrap(){
            'f'=>{
                *index+=1;
                if *index>=string.len(){
                    return Err("Formula not well formatted: Found no character while trying to read a fresh variable!".to_string());
                }
                match *string.get(*index).unwrap(){
                    '1'|'2'|'3'|'4'|'5'|'6'|'7'|'8'|'9'=>{
                        let mut number=*string.get(*index).unwrap() as i32 - '0' as i32;
                        loop{
                            *index+=1;
                            if *index>=string.len(){
                                return Err("Formula not well formatted: Found no character while trying to read a fresh variable!".to_string());
                            }
                            match *string.get(*index).unwrap() {
                                '0'|'1'|'2'|'3'|'4'|'5'|'6'|'7'|'8'|'9'=>{
                                    let digit=*string.get(*index).unwrap() as i32 - '0' as i32;
                                    number=number*10+digit;
                                },
                                _=>{
                                    break;
                                }
                            }
                        }
                        return Ok(-number);
                    },
                    _=>{
                        let error=format!("Formula not well formatted: Invalid character found while trying to read a fresh variable!
                            At position {} of {}
                            Expected a number
                            Found \"{}\" instead",*index,string.into_iter().collect::<String>(),*string.get(*index).unwrap());
                        return Err(error);
                    }
                }
            },
            '0'=>{
                *index+=1;
                if *index>=string.len(){
                    return Err("Formula not well formatted: Found no character while trying to read a 0 variable!".to_string());
                }
                return Ok(0);
            },
            '1'|'2'|'3'|'4'|'5'|'6'|'7'|'8'|'9'=>{
                let mut number=*string.get(*index).unwrap() as i32 - '0' as i32;
                loop{
                    *index+=1;
                    if *index>=string.len(){
                        return Err("Formula not well formatted: Found no character while trying to read an original variable!".to_string());
                    }
                    match *string.get(*index).unwrap() {
                        '0'|'1'|'2'|'3'|'4'|'5'|'6'|'7'|'8'|'9'=>{
                            let digit=*string.get(*index).unwrap() as i32 - '0' as i32;
                            number=number*10+digit;
                        },
                        _=>{
                            break;
                        }
                    }
                }
                return Ok(number);
            },
            _=>{
                let error=format!("Formula not well formatted: Invalid character found while trying to read a variable!
                    At position {} of {}
                    Expected \"f\" or a number
                    Found \"{}\" instead",*index,string.into_iter().collect::<String>(),*string.get(*index).unwrap());
                return Err(error);
            }
        }
    }

    fn read_atom(string: &Vec<char>, index: &mut usize)->Result<Node,String>{
        *index+=1;
        if *index>=string.len(){
            return Err("Formula not well formatted: Found no character while trying to read an atom!".to_string());
        }
        while *string.get(*index).unwrap()==' '{
            *index+=1;
            if *index>=string.len(){
                return Err("Formula not well formatted: Found no character while trying to read an atom!".to_string());
            }
        }
        match *string.get(*index).unwrap() {
            'f'|'0'|'1'|'2'|'3'|'4'|'5'|'6'|'7'|'8'|'9'=>{
                return match Self::read_variable_name(string,index){
                    Ok(x)=>Ok(Node::Variable(x)),
                    Err(e)=>Err(e)
                };
            },
            '-'=>{
                return match Self::read_atom(string,index){
                    Ok(atom)=>Ok(Node::Not(Rc::new(RefCell::new(Formula::new(atom))))),
                    Err(e)=>Err(e)
                };
            },
            'A'=>{
                *index+=1;
                if *index>=string.len(){
                    return Err("Formula not well formatted: Found no character while trying to read a universal quantifier!".to_string());
                }
                let var= match Self::read_variable_name(string,index){
                    Ok(x)=>x,
                    Err(e)=>{return Err(e);}
                };
                while *string.get(*index).unwrap()==' '{
                    *index+=1;
                    if *index>=string.len(){
                        return Err("Formula not well formatted: Found no character while trying to read a variable!".to_string());
                    }
                }
                match *string.get(*index).unwrap(){
                    '.'=>{
                        let next_atom=match Self::read_atom(string, index){
                            Ok(atom)=>atom,
                            Err(e)=>{return Err(e);}
                        };
                        return Ok(Node::ForEach(var, Rc::new(RefCell::new(Formula::new(next_atom)))));
                    },
                    _=>{
                        let error=format!("Formula not well formatted: Invalid character found after universal quantifier!
                            At position {} of {}
                            Expected \".\"
                            Found \"{}\" instead",*index,string.into_iter().collect::<String>(),*string.get(*index).unwrap());
                        return Err(error);
                    }
                }
            },
            'E'=>{
                *index+=1;
                if *index>=string.len(){
                    return Err("Formula not well formatted: Found no character while trying to read an existential quantifier!".to_string());
                }
                let var= match Self::read_variable_name(string,index){
                    Ok(x)=>x,
                    Err(e)=>{return Err(e);}
                };
                while *string.get(*index).unwrap()==' '{
                    *index+=1;
                    if *index>=string.len(){
                        return Err("Formula not well formatted: Found no character while trying to read a variable!".to_string());
                    }
                }
                match *string.get(*index).unwrap(){
                    '.'=>{
                        let next_atom=match Self::read_atom(string, index){
                            Ok(atom)=>atom,
                            Err(e)=>{return Err(e);}
                        };
                        return Ok(Node::ForEach(var, Rc::new(RefCell::new(Formula::new(next_atom)))));
                    },
                    _=>{
                        let error=format!("Formula not well formatted: Invalid character found after existential quantifier!
                            At position {} of {}
                            Expected \".\"
                            Found \"{}\" instead",*index,string.into_iter().collect::<String>(),*string.get(*index).unwrap());
                        return Err(error);
                    }
                }
            },
            'T'=>{
                *index+=1;
                if *index>=string.len(){
                    return Err("Formula not well formatted: Found no character after True atom!".to_string());
                }
                return Ok(Node::True);
            },
            'F'=>{
                *index+=1;
                if *index>=string.len(){
                    return Err("Formula not well formatted: Found no character after False atom!".to_string());
                }
                return Ok(Node::False);
            },
            '('=>{
                return Self::from_string_at_char(string, index);
            },
            _=>{
                let error=format!("Formula not well formatted: Invalid character found in the beginning of an atom!
                    At position {} of {}
                    Expected quantifier (A,E) or truth value (T,F) or negation (-) or variable number
                    Found \"{}\" instead",*index,string.into_iter().collect::<String>(),*string.get(*index).unwrap());
                return Err(error);
            }
        }
    }

    pub fn remove_quantifiers(&mut self){
        match &mut self.root{
            Node::Exists(var,formula)=>{
                (*formula.borrow_mut()).remove_quantifiers();
                let serial=(*formula.borrow()).to_string();
                let mut left=Formula::from_string(serial.clone()).unwrap();
                let mut right=Formula::from_string(serial).unwrap();
                left.set_truth(*var, true);
                right.set_truth(*var, false);
                let vector=vec![Rc::new(RefCell::new(left)),Rc::new(RefCell::new(right))];
                self.root=Node::Or(vector);
            },
            Node::ForEach(var,formula)=>{
                (*formula.borrow_mut()).remove_quantifiers();
                let serial=(*formula.borrow()).to_string();
                let mut left=Formula::from_string(serial.clone()).unwrap();
                let mut right=Formula::from_string(serial).unwrap();
                left.set_truth(*var, true);
                right.set_truth(*var, false);
                let vector=vec![Rc::new(RefCell::new(left)),Rc::new(RefCell::new(right))];
                self.root=Node::And(vector);
            },
            Node::And(vec)|
            Node::Or(vec)=>{
                for formula in vec{
                    (*formula.borrow_mut()).remove_quantifiers();
                }
            },
            Node::Implies(a,b)|
            Node::IsImpliedBy(a,b)|
            Node::Iff(a,b)|
            Node::Xor(a,b)=>{
                (*a.borrow_mut()).remove_quantifiers();
                (*b.borrow_mut()).remove_quantifiers();
            },
            Node::Not(x)=>{
                (*x.borrow_mut()).remove_quantifiers();
            },
            _=>{return;}
        }
    }

    pub fn simplify_truth(&mut self){
        match &mut self.root{
            Node::Variable(_)=>{
                return;
            },
            Node::Not(formula)=>{
                (formula.borrow_mut()).simplify_truth();
                let mut new_node:Option<Node>=None;
                match (*formula.borrow()).root {
                    Node::True=>{
                        new_node=Some(Node::False);
                    },
                    Node::False=>{
                        new_node=Some(Node::True);
                    },
                    _=>{}
                };
                if new_node.is_some(){
                    self.root=new_node.unwrap();
                }
            },
            Node::Exists(_var,formula)|
            Node::ForEach(_var,formula)=>{
                (formula.borrow_mut()).simplify_truth();
                let mut new_node:Option<Node>=None;
                match (*formula.borrow()).root {
                    Node::True=>{
                        new_node=Some(Node::True);
                    },
                    Node::False=>{
                        new_node=Some(Node::False);
                    },
                    _=>{}
                };
                if new_node.is_some(){
                    self.root=new_node.unwrap();
                }
            },
            Node::Xor(a,b)=>{
                (a.borrow_mut()).simplify_truth();
                (b.borrow_mut()).simplify_truth();
                let mut new_node:Option<Node>=None;
                match &(*a.borrow()).root{
                    Node::True=>{
                        match &(*b.borrow()).root{
                            Node::True=>{
                                new_node=Some(Node::False);
                            },
                            Node::False=>{
                                new_node=Some(Node::True);
                            },
                            _=>{
                                new_node=Some(Node::Not(Rc::clone(&b)));
                            }
                        };
                    },
                    Node::False=>{
                        match &(*b.borrow()).root{
                            Node::True=>{
                                new_node=Some(Node::True);
                            },
                            Node::False=>{
                                new_node=Some(Node::False);
                            },
                            _=>{
                                new_node=Some((*b.borrow()).root.clone());
                            }
                        };
                    },
                    _=>{
                        match &(*b.borrow()).root{
                            Node::True=>{
                                new_node=Some(Node::Not(Rc::clone(&a)));
                            },
                            Node::False=>{
                                new_node=Some((*a.borrow()).root.clone());
                            },
                            _=>{}
                        };
                    }
                };
                if new_node.is_some(){
                    self.root=new_node.unwrap();
                }
            },
            Node::Implies(a,b)=>{
                (a.borrow_mut()).simplify_truth();
                (b.borrow_mut()).simplify_truth();
                let mut new_node:Option<Node>=None;
                match &(*a.borrow()).root{
                    Node::True=>{
                        match &(*b.borrow()).root{
                            Node::True=>{
                                new_node=Some(Node::True);
                            },
                            Node::False=>{
                                new_node=Some(Node::False);
                            },
                            _=>{
                                new_node=Some((*b.borrow()).root.clone());
                            }
                        };
                    },
                    Node::False=>{
                        new_node=Some(Node::True);
                    },
                    _=>{
                        match &(*b.borrow()).root{
                            Node::True=>{
                                new_node=Some(Node::True);
                            },
                            Node::False=>{
                                new_node=Some(Node::Not(Rc::clone(&a)));
                            },
                            _=>{}
                        };
                    }
                };
                if new_node.is_some(){
                    self.root=new_node.unwrap();
                }
            },
            Node::IsImpliedBy(a,b)=>{
                (a.borrow_mut()).simplify_truth();
                (b.borrow_mut()).simplify_truth();
                let mut new_node:Option<Node>=None;
                match &(*b.borrow()).root{
                    Node::True=>{
                        match &(*a.borrow()).root{
                            Node::True=>{
                                new_node=Some(Node::True);
                            },
                            Node::False=>{
                                new_node=Some(Node::False);
                            },
                            _=>{
                                new_node=Some((*a.borrow()).root.clone());
                            }
                        };
                    },
                    Node::False=>{
                        new_node=Some(Node::True);
                    },
                    _=>{
                        match &(*a.borrow()).root{
                            Node::True=>{
                                new_node=Some(Node::True);
                            },
                            Node::False=>{
                                new_node=Some(Node::Not(Rc::clone(&b)));
                            },
                            _=>{}
                        };
                    }
                };
                if new_node.is_some(){
                    self.root=new_node.unwrap();
                }
            },
            Node::Iff(a,b)=>{
                (a.borrow_mut()).simplify_truth();
                (b.borrow_mut()).simplify_truth();
                let mut new_node:Option<Node>=None;
                match &(*a.borrow()).root{
                    Node::True=>{
                        match &(*b.borrow()).root{
                            Node::True=>{
                                new_node=Some(Node::True);
                            },
                            Node::False=>{
                                new_node=Some(Node::False);
                            },
                            _=>{
                                new_node=Some((*b.borrow()).root.clone());
                            }
                        };
                    },
                    Node::False=>{
                        match &(*b.borrow()).root{
                            Node::True=>{
                                new_node=Some(Node::False);
                            },
                            Node::False=>{
                                new_node=Some(Node::True);
                            },
                            _=>{
                                new_node=Some(Node::Not(Rc::clone(&b)));
                            }
                        };
                    },
                    _=>{
                        match &(*b.borrow()).root{
                            Node::True=>{
                                new_node=Some((*a.borrow()).root.clone());
                            },
                            Node::False=>{
                                new_node=Some(Node::Not(Rc::clone(&a)));
                            },
                            _=>{}
                        };
                    }
                };
                if new_node.is_some(){
                    self.root=new_node.unwrap();
                }
            },
            Node::And(vec)=>{
                let mut new_node:Option<Node>=None;
                let mut index_to_remove:Vec<usize>=vec![];
                for i in 0..vec.len(){
                    let formula=vec.get(i).unwrap();
                    (formula.borrow_mut()).simplify_truth();
                    match (*formula.borrow()).root {
                        Node::True=>{
                            index_to_remove.push(i);
                        },
                        Node::False=>{
                            new_node=Some(Node::False);
                            break;
                        },
                        _=>{}
                    };
                }
                if new_node.is_some(){
                    self.root=new_node.unwrap();
                }else{
                    index_to_remove.reverse();
                    for index in index_to_remove{
                        vec.remove(index);
                    }
                    if vec.len()==0{
                        self.root=Node::True;
                    }else if vec.len()==1{
                        let last_node=vec.remove(0);
                        self.root=(*last_node.borrow()).root.clone();
                    }
                }
            },
            Node::Or(vec)=>{
                let mut new_node:Option<Node>=None;
                let mut index_to_remove:Vec<usize>=vec![];
                for i in 0..vec.len(){
                    let formula=vec.get(i).unwrap();
                    (formula.borrow_mut()).simplify_truth();
                    match (*formula.borrow()).root {
                        Node::False=>{
                            index_to_remove.push(i);
                        },
                        Node::True=>{
                            new_node=Some(Node::True);
                            break;
                        },
                        _=>{}
                    };
                }
                if new_node.is_some(){
                    self.root=new_node.unwrap();
                }else{
                    index_to_remove.reverse();
                    for index in index_to_remove{
                        vec.remove(index);
                    }
                    if vec.len()==0{
                        self.root=Node::False;
                    }else if vec.len()==1{
                        let last_node=vec.remove(0);
                        self.root=(*last_node.borrow()).root.clone();
                    }
                }
            },
            Node::True|Node::False=>{return;}
        };       
    }

    pub fn set_truth(&mut self, variable:i32, truth:bool){
        match &mut self.root{
            Node::Variable(y)=>{
                if *y==variable{
                    if truth{
                        self.root=Node::True;
                    }else{
                        self.root=Node::False;
                    }
                }
            },
            Node::Not(formula)=>{
                (formula.borrow_mut()).set_truth(variable,truth);
            },
            Node::Exists(_var,formula)|
            Node::ForEach(_var,formula)=>{
                (formula.borrow_mut()).set_truth(variable,truth);
            },
            Node::Xor(a,b)|
            Node::Implies(a,b)|
            Node::IsImpliedBy(a,b)|
            Node::Iff(a,b)=>{
                (a.borrow_mut()).set_truth(variable,truth);
                (b.borrow_mut()).set_truth(variable,truth);
            },
            Node::And(vec)|
            Node::Or(vec)=>{
                for x in vec{
                    (*x.borrow_mut()).set_truth(variable,truth);
                }
            },
            Node::True|Node::False=>{}
        };
        self.simplify_truth();
    }

    pub fn make_nnf(&mut self){
        self.remove_quantifiers();
        self.simplify_truth();
        self.flatten();
        self.remove_impl();
        self.flatten();
        self.push_neg_down();
        self.flatten();
    }

    pub fn flatten(&mut self){
        self.flatten_and();
        self.flatten_or();
    }

    fn flatten_or(&mut self){
        match &mut self.root{
            Node::Or(old_vec)=>{
                loop{
                    //scan
                    let mut vec:Vec<usize>=vec![];
                    for i in 0..old_vec.len(){
                        match (*old_vec.get(i).unwrap().borrow()).root{
                            Node::Or(_)=>{vec.push(i);},
                            _=>{}
                        }
                    }
                    vec.reverse();
                    //check
                    if vec.len()==0{
                        break;
                    }
                    //flatten
                    for index in vec{
                        let elem=old_vec.remove(index);
                        match &(*elem.borrow()).root{
                            Node::Or(atoms)=>{
                                for atom in atoms.iter(){
                                    old_vec.push(Rc::clone(atom));
                                }
                            },
                            _=>{unreachable!();}
                        };
                    }
                }
            },
            _=>{}
        }
        //apply recursively on all members
        match &mut self.root{
            Node::And(vector)|
            Node::Or(vector)=>{
                for x in vector.iter(){
                    (*x.borrow_mut()).flatten_or();
                }
            },
            Node::Iff(a,b)|
            Node::Implies(a,b)|
            Node::Xor(a,b)|
            Node::IsImpliedBy(a,b)=>{
                (*a.borrow_mut()).flatten_or();
                (*b.borrow_mut()).flatten_or();
            },
            Node::Not(a)=>{
                (*a.borrow_mut()).flatten_or();
            },
            Node::Variable(_)|Node::True|Node::False=>{return;},
            Node::Exists(_,f)|
            Node::ForEach(_,f)=>{
                (*f.borrow_mut()).flatten_and();
            }
        };
    }

    fn flatten_and(&mut self){
        match &mut self.root{
            Node::And(old_vec)=>{
                loop{
                    //scan
                    let mut vec:Vec<usize>=vec![];
                    for i in 0..old_vec.len(){
                        match (*old_vec.get(i).unwrap().borrow()).root{
                            Node::And(_)=>{vec.push(i);},
                            _=>{}
                        }
                    }
                    vec.reverse();
                    //check
                    if vec.len()==0{
                        break;
                    }
                    //flatten
                    for index in vec{
                        let elem=old_vec.remove(index);
                        match &(*elem.borrow()).root{
                            Node::And(atoms)=>{
                                for atom in atoms.iter(){
                                    old_vec.push(Rc::clone(atom));
                                }
                            },
                            _=>{unreachable!();}
                        };
                    }
                }
            },
            _=>{}
        }
        //apply recursively on all members
        match &mut self.root{
            Node::And(vector)|
            Node::Or(vector)=>{
                for x in vector.iter(){
                    (*x.borrow_mut()).flatten_and();
                }
            },
            Node::Iff(a,b)|
            Node::Implies(a,b)|
            Node::Xor(a,b)|
            Node::IsImpliedBy(a,b)=>{
                (*a.borrow_mut()).flatten_and();
                (*b.borrow_mut()).flatten_and();
            },
            Node::Not(a)=>{
                (*a.borrow_mut()).flatten_and();
            },
            Node::Variable(_)|Node::True|Node::False=>{return;},
            Node::Exists(_,f)|
            Node::ForEach(_,f)=>{
                (*f.borrow_mut()).flatten_and();
            }
        };
    }

    fn remove_impl(&mut self){
        let mut new_node:Option<Node>=None;
        match &mut self.root{
            Node::And(vec)|
            Node::Or(vec)=>{
                for x in vec.iter(){
                    (*x.borrow_mut()).remove_impl();
                }
            },
            Node::Xor(a,b)=>{
                // a%b |= a = -b
                let mut borrow_left=a.borrow_mut();
                borrow_left.remove_impl();
                let mut borrow_right=b.borrow_mut();
                borrow_right.remove_impl();
                let right_vec=vec![
                    Rc::clone(&a),
                    Rc::new(RefCell::new(Formula::new(Node::Not(Rc::clone(&b)))))];
                let right_node=Node::Or(right_vec);
                let left_vec=vec![
                    Rc::new(RefCell::new(Formula::new(Node::Not(Rc::clone(&a))))),
                    Rc::clone(&b)];
                let left_node=Node::Not(Rc::new(RefCell::new(Formula::new(Node::Or(left_vec)))));
                let new_vec=vec![
                    Rc::new(RefCell::new(Formula::new(left_node))),
                    Rc::new(RefCell::new(Formula::new(right_node))) ];
                new_node=Some(Node::And(new_vec));
            },
            Node::Implies(a,b)=>{
                // a>b |= -a*b
                let mut borrow_left=a.borrow_mut();
                borrow_left.remove_impl();
                let mut borrow_right=b.borrow_mut();
                borrow_right.remove_impl();
                let new_vec=vec![
                    Rc::new(RefCell::new(Formula::new(Node::Not(Rc::clone(&a))))),
                    Rc::clone(&b)];
                new_node=Some(Node::Or(new_vec));
            },
            Node::IsImpliedBy(a,b)=>{
                // a<b |= a*-b
                let mut borrow_left=a.borrow_mut();
                borrow_left.remove_impl();
                let mut borrow_right=b.borrow_mut();
                borrow_right.remove_impl();
                let new_vec=vec![
                    Rc::clone(&a),
                    Rc::new(RefCell::new(Formula::new(Node::Not(Rc::clone(&b)))))];
                new_node=Some(Node::Or(new_vec));
            },
            Node::Iff(a,b)=>{
                // a=b |= (a>b)+(a<b) 
                let mut borrow_left=a.borrow_mut();
                borrow_left.remove_impl();
                let mut borrow_right=b.borrow_mut();
                borrow_right.remove_impl();
                let right_vec=vec![
                    Rc::clone(&a),
                    Rc::new(RefCell::new(Formula::new(Node::Not(Rc::clone(&b)))))];
                let right_node=Node::Or(right_vec);
                let left_vec=vec![
                    Rc::new(RefCell::new(Formula::new(Node::Not(Rc::clone(&a))))),
                    Rc::clone(&b)];
                let left_node=Node::Or(left_vec);
                let full_vec=vec![
                    Rc::new(RefCell::new(Formula::new(left_node))),
                    Rc::new(RefCell::new(Formula::new(right_node)))];
                new_node=Some(Node::And(full_vec));
            },
            Node::Not(x)=>{
                (x.borrow_mut()).remove_impl();
            },
            Node::Exists(_x,f)|
            Node::ForEach(_x,f)=>{
                (f.borrow_mut()).remove_impl();
            }
            _=>{}
        }
        if new_node.is_some(){
            self.root=new_node.unwrap();
        }
    }

    fn push_neg_down(&mut self){
        let mut new_node:Option<Node>=None;
        let mut done=false;
        match &self.root{
            Node::And(_)|Node::Or(_)=>{},
            Node::Variable(_)=>{done=true;},
            Node::True|Node::False=>{done=true;},
            Node::Not(f)=>{
                let borrowed_formula=f.borrow_mut();
                match &borrowed_formula.root{
                    Node::And(old_vec)=>{
                        let mut new_vec:Vec<Link>=vec![];
                        for x in old_vec{
                            new_vec.push(Rc::new(RefCell::new(Formula::new(Node::Not(Rc::clone(&x))))));
                        }
                        new_node=Some(Node::Or(new_vec));
                    },
                    Node::Or(old_vec)=>{
                        let mut new_vec:Vec<Link>=vec![];
                        for x in old_vec{
                            new_vec.push(
                                Rc::new(RefCell::new(Formula::new(
                                    Node::Not(Rc::clone(&x))
                                ))));
                        }
                        new_node=Some(Node::And(new_vec));
                    },
                    Node::Not(x)=>{// double negation
                        let borrowed_inside=x.borrow_mut();
                        match &borrowed_inside.root{
                            Node::And(old_vec)=>{
                                let mut new_vec:Vec<Link>=vec![];
                                for x in old_vec{
                                    new_vec.push(Rc::clone(&x));
                                }
                                new_node=Some(Node::And(new_vec));
                            },
                            Node::Or(old_vec)=>{
                                let mut new_vec:Vec<Link>=vec![];
                                for x in old_vec{
                                    new_vec.push(Rc::clone(&x));
                                }
                                new_node=Some(Node::Or(new_vec));
                            },
                            Node::Not(x)=>{
                                new_node=Some(Node::Not(
                                    Rc::clone(x)
                                ));
                            },
                            Node::Variable(x)=>{
                                new_node=Some(Node::Variable(*x));
                                done=true;
                            },
                            Node::True=>{new_node=Some(Node::True);},
                            Node::False=>{new_node=Some(Node::False);},
                            _=>{panic!("Unwanted node type while pushing negations");}
                        }
                    },
                    Node::Variable(_)=>{done=true;},
                    Node::True=>{new_node=Some(Node::False);done=true;},
                    Node::False=>{new_node=Some(Node::True);done=true;},
                    _=>{panic!("1 - Unwanted node type while pushing negations 
                        (remember that this function must always be called after removing quantifiers and implications)");}
                }
            },
            _=>{panic!("2 - Unwanted node type while pushing negations
                (remember that this function must always be called after removing quantifiers and implications)");}
        }
        if new_node.is_some(){
            self.root=new_node.unwrap();
        }
        if done{return;}
        match &self.root{
            Node::And(vec)|Node::Or(vec)=>{
                for x in vec{
                    (*x.borrow_mut()).push_neg_down();
                }
            },
            Node::Not(_)=>{
                self.push_neg_down();
            },
            _=>{panic!("Unwanted node type while pushing negations
                (remember that this function must always be called after removing quantifiers and implications)");} 
        }
    }

    pub fn make_cnf_label(&mut self){
        if self.is_cnf(){
            return;
        }
        self.make_nnf();
        self.cnf_label();
        self.flatten();
    }

    pub fn is_cnf(&self)->bool{
        match &self.root{
            Node::And(vector)=>{
                for x in vector.iter(){
                    if !(*x.borrow()).is_shallow(){
                        return false;
                    }
                }
                return true;
            },
            Node::Not(x)=>{
                match (*x.borrow()).root{
                    Node::Variable(_)|Node::True|Node::False=>{return true;},
                    _=>{return false;}
                }
            },
            Node::Variable(_)|
            Node::True|
            Node::False=>{return true;},
            _=>{return false;}
        }
    }

    pub fn is_true(&self)->bool{
        match &self.root{
            Node::True=>{true},
            _=>{false}
        }
    }

    pub fn is_false(&self)->bool{
        match &self.root{
            Node::False=>{true},
            _=>{false}
        }
    }

    fn cnf_label(&mut self){
        let mut next_fresh=-1;
        if self.is_false() || self.is_true(){
            return;
        }
        let mut clause_vector:Vec<Link>=vec![];
        self.cnf_label_recursive(&mut next_fresh, &mut clause_vector);
        match &self.root{
            Node::Variable(fresh)=>{
                clause_vector.push(Rc::new(RefCell::new(Formula::new(Node::Variable(*fresh)))));
            },
            _=>{unreachable!();}
        }
        self.root=Node::And(clause_vector);
    }

    fn cnf_label_recursive(&mut self, next_fresh:&mut i32, clause_vector: &mut Vec<Link>){
        // bottom up approach
        // apply recursively
        if !self.is_shallow(){
            match &self.root{
                Node::And(vector)|
                Node::Or(vector)=>{
                    for x in vector.iter(){
                        (*x.borrow_mut()).cnf_label_recursive(next_fresh,clause_vector);
                    }
                },
                _=>{unreachable!();}
            }
        }
        // consume operator
        let mut new_node:Option<Node>=None;
        match &mut self.root{
            Node::And(vector)=>{
                while vector.len()>1{
                    let i=vector.remove(vector.len()-1);
                    let j=vector.remove(vector.len()-1);
                    let not_i=match &(*i.borrow()).root{
                        Node::Not(internal)=>{
                            Rc::clone(&internal)
                        },
                        Node::Variable(_)=>{
                            Rc::new(RefCell::new(Formula::new(Node::Not(Rc::clone(&i)))))
                        },
                        _=>{unreachable!();}
                    };
                    let not_j=match &(*j.borrow()).root{
                        Node::Not(internal)=>{
                            Rc::clone(&internal)
                        },
                        Node::Variable(_)=>{
                            Rc::new(RefCell::new(Formula::new(Node::Not(Rc::clone(&j)))))
                        },
                        _=>{unreachable!();}
                    };
                    let next_variable=Rc::new(RefCell::new(Formula::new(Node::Variable(*next_fresh))));
                    // -B * i
                    let vec_first_inside=vec![
                        Rc::new(RefCell::new(Formula::new(Node::Not(
                            Rc::clone(&next_variable)
                        )))),
                        Rc::clone(&i)];
                    clause_vector.push(
                        Rc::new(RefCell::new(Formula::new(Node::Or(vec_first_inside))))
                    );
                    // -B * j
                    let vec_second_inside=vec![
                        Rc::new(RefCell::new(Formula::new(Node::Not(
                            Rc::clone(&next_variable)
                        )))),
                        Rc::clone(&j)];
                    clause_vector.push(
                        Rc::new(RefCell::new(Formula::new(Node::Or(vec_second_inside))))
                    );
                    // B * -i * -j
                    let vec_third_inside=vec![
                        Rc::clone(&next_variable),
                        Rc::clone(&not_i),
                        Rc::clone(&not_j)];
                    clause_vector.push(
                        Rc::new(RefCell::new(Formula::new(Node::Or(vec_third_inside))))
                    );
                    vector.push(Rc::clone(&next_variable));
                    *next_fresh-=1;
                }
                let last_element=vector.remove(0);
                new_node=Some((*last_element.borrow()).root.clone());
            },
            Node::Or(vector)=>{
                while vector.len()>1{
                    let i=vector.remove(vector.len()-1);
                    let j=vector.remove(vector.len()-1);
                    let not_i=match &(*i.borrow()).root{
                        Node::Not(internal)=>{
                            Rc::clone(&internal)
                        },
                        Node::Variable(_)=>{
                            Rc::new(RefCell::new(Formula::new(Node::Not(Rc::clone(&i)))))
                        },
                        _=>{unreachable!();}
                    };
                    let not_j=match &(*j.borrow()).root{
                        Node::Not(internal)=>{
                            Rc::clone(&internal)
                        },
                        Node::Variable(_)=>{
                            Rc::new(RefCell::new(Formula::new(Node::Not(Rc::clone(&j)))))
                        },
                        _=>{unreachable!();}
                    };
                    let next_variable=Rc::new(RefCell::new(Formula::new(Node::Variable(*next_fresh))));
                    // B * -i
                    let vec_first_inside=vec![
                        Rc::clone(&next_variable),
                        Rc::clone(&not_i)];
                    clause_vector.push(
                        Rc::new(RefCell::new(Formula::new(Node::Or(vec_first_inside))))
                    );
                    // B * -j
                    let vec_second_inside=vec![
                        Rc::clone(&next_variable),
                        Rc::clone(&not_j)];
                    clause_vector.push(
                        Rc::new(RefCell::new(Formula::new(Node::Or(vec_second_inside))))
                    );
                    // -B * i * j
                    let vec_third_inside=vec![
                        Rc::new(RefCell::new(Formula::new(Node::Not(
                            Rc::clone(&next_variable)
                        )))),
                        Rc::clone(&i),
                        Rc::clone(&j)];
                    clause_vector.push(
                        Rc::new(RefCell::new(Formula::new(Node::Or(vec_third_inside))))
                    );
                    vector.push(Rc::clone(&next_variable));
                    *next_fresh-=1;
                }
                let last_element=vector.remove(0);
                new_node=Some((*last_element.borrow()).root.clone());
            },
            _=>{}
        }
        if new_node.is_some(){
            self.root=new_node.unwrap();
        }
    }

    fn is_shallow(&self)->bool{
        match &self.root{
            Node::And(vector)|
            Node::Or(vector)=>{
                for x in vector.iter(){
                    if !(*x.borrow()).is_atom(){
                        return false;
                    }
                }
                return true;
            },
            Node::Not(x)=>{
                match (*x.borrow()).root{
                    Node::Variable(_)=>{return true;},
                    _=>{return false;}
                }
            },
            Node::Variable(_)=>{return true;},
            _=>{return false;}
        }
    }

    fn is_atom(&self)->bool{
        match &self.root{
            Node::Not(x)=>{
                match (*x.borrow()).root{
                    Node::Variable(_)=>{return true;},
                    _=>{return false;}
                }
            },
            Node::Variable(_)=>{return true;},
            _=>{return false;}
        }
    }

    fn find_variables(&self)->HashSet<i32>{
        let mut set=HashSet::new();
        self.find_variables_recursive(&mut set);
        return set;
    }

    fn find_variables_recursive(&self,set:&mut HashSet<i32>){
        match &self.root{
            Node::And(vec)|
            Node::Or(vec)=>{
                for x in vec.iter(){
                    (*x.borrow()).find_variables_recursive(set);
                }
            },
            Node::Iff(a,b)|
            Node::Implies(a,b)|
            Node::IsImpliedBy(a,b)|
            Node::Xor(a,b)=>{
                (*a.borrow()).find_variables_recursive(set);
                (*b.borrow()).find_variables_recursive(set);
            },
            Node::Not(a)=>{
                (*a.borrow()).find_variables_recursive(set);
            },
            Node::Variable(i)=>{set.insert(*i);},
            Node::Exists(a,f)|
            Node::ForEach(a,f)=>{
                set.insert(*a);
                (*f.borrow_mut()).find_variables_recursive(set);
            },
            Node::True|Node::False=>{
                return;
            }
        };
    }

    pub fn to_string(&self) -> String{
        let mut res:String="".to_string();
        match &self.root{
            Node::Variable(x)=>{
                if *x>=0{
                    let str_var=x.to_string();
                    res.push_str(&str_var);
                }else{
                    let y=-*x;
                    res.push_str("f");
                    let str_var=y.to_string();
                    res.push_str(&str_var);
                }
            },
            Node::True=>{
                res.push_str("T");
            },
            Node::False=>{
                res.push_str("F");
            },
            Node::And(vec)=>{
                res.push_str("(");
                for i in 0..(vec.len()-1){
                    let token=(vec.get(i).unwrap().borrow()).to_string();
                    res.push_str(&token);
                    res.push_str("+");
                }
                let token=(vec.get(vec.len()-1).unwrap().borrow()).to_string();
                res.push_str(&token);
                res.push_str(")");
            },
            Node::Or(vec)=>{
                res.push_str("(");
                for i in 0..(vec.len()-1){
                    let token=(vec.get(i).unwrap().borrow()).to_string();
                    res.push_str(&token);
                    res.push_str("*");
                }
                let token=(vec.get(vec.len()-1).unwrap().borrow()).to_string();
                res.push_str(&token);
                res.push_str(")");
            },
            Node::Xor(a,b)=>{
                res.push_str("(");
                let left_str=(a.borrow()).to_string();
                res.push_str(&left_str);
                res.push_str("%");
                let right_str=(b.borrow()).to_string();
                res.push_str(&right_str);
                res.push_str(")");
            },
            Node::Iff(a,b)=>{
                res.push_str("(");
                let left_str=(a.borrow()).to_string();
                res.push_str(&left_str);
                res.push_str("=");
                let right_str=(b.borrow()).to_string();
                res.push_str(&right_str);
                res.push_str(")");
            },
            Node::Implies(a,b)=>{
                res.push_str("(");
                let left_str=(a.borrow()).to_string();
                res.push_str(&left_str);
                res.push_str(">");
                let right_str=(b.borrow()).to_string();
                res.push_str(&right_str);
                res.push_str(")");
            },
            Node::IsImpliedBy(a,b)=>{
                res.push_str("(");
                let left_str=(a.borrow()).to_string();
                res.push_str(&left_str);
                res.push_str("+");
                let right_str=(b.borrow()).to_string();
                res.push_str(&right_str);
                res.push_str(")");
            },
            Node::Not(a)=>{
                res.push_str("-");
                let for_str=(a.borrow()).to_string();
                res.push_str(&for_str);
            },
            Node::Exists(x,f)=>{
                res.push_str("E");
                if *x>=0{
                    let str_var=x.to_string();
                    res.push_str(&str_var);
                }else{
                    let y=-*x;
                    res.push_str("f");
                    let str_var=y.to_string();
                    res.push_str(&str_var);
                }
                res.push_str(".");
                let formula_string=(*f.borrow()).to_string();
                res.push_str(&formula_string);
            },
            Node::ForEach(x,f)=>{
                res.push_str("A");
                if *x>=0{
                    let str_var=x.to_string();
                    res.push_str(&str_var);
                }else{
                    let y=-*x;
                    res.push_str("f");
                    let str_var=y.to_string();
                    res.push_str(&str_var);
                }
                res.push_str(".");
                let formula_string=(*f.borrow()).to_string();
                res.push_str(&formula_string);
            }
        }
        return res;
    } 

    pub fn to_cnf_representation(&self)->CNF{
        if !self.is_cnf(){
            let mut cloned:Formula=self.clone();
            cloned.make_cnf_label();
            return cloned.to_cnf_representation();
        }
        let mut formula=CNF::new();
        match &self.root{
            Node::And(clauses)=>{
                for clause in clauses.iter(){
                    let mut current_clause=Clause::new();
                    match &(*clause.borrow()).root{
                        Node::Or(literals)=>{
                            for literal in literals.iter(){
                                match &(*literal.borrow()).root{
                                    Node::Variable(x)=>{
                                        current_clause.add_literal(Literal::new(crate::sat::Polarity::Positive,*x));
                                    },
                                    Node::Not(x)=>{
                                        match &(*x.borrow()).root{
                                            Node::Variable(y)=>{
                                                current_clause.add_literal(Literal::new(crate::sat::Polarity::Negative,*y));
                                            },
                                            _=>{unreachable!();}
                                        }
                                    },
                                    _=>{unreachable!();}
                                }
                            }
                        },
                        Node::Variable(x)=>{
                            current_clause.add_literal(Literal::new(crate::sat::Polarity::Positive,*x));
                        },
                        Node::Not(x)=>{
                            match &(*x.borrow()).root{
                                Node::Variable(y)=>{
                                    current_clause.add_literal(Literal::new(crate::sat::Polarity::Negative,*y));
                                },
                                _=>{unreachable!();}
                            }
                        }
                        _=>{unreachable!();}
                    }
                    formula.add_clause(current_clause);
                }
            },
            Node::Variable(x)=>{
                let mut clause=Clause::new();
                let literal=Literal { variable: *x, polarity: crate::sat::Polarity::Positive };
                clause.add_literal(literal);
                formula.add_clause(clause);
            },
            Node::Not(x)=>{
                let mut clause=Clause::new();
                match &(*x.borrow()).root{
                    Node::Variable(y)=>{
                        clause.add_literal(Literal::new(crate::sat::Polarity::Negative,*y));
                    },
                    _=>{unreachable!();}
                }
                formula.add_clause(clause)
            },
            _=>{unreachable!();}
        }
        return formula;
    }
}

impl Clone for Formula{
    fn clone(&self)->Self{
        let string=self.to_string();
        Self::from_string(string).unwrap()
    }
}
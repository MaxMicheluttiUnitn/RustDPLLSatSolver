use crate::{formula::BooleanFormula, operators::{NEGATION_OPERATOR_SYMBOL, FRESH_VARIABLE_SYMBOL, OR_OPERATOR_SYMBOL, AND_OPERATOR_SYMBOL}};
use std::collections::{HashSet,HashMap};

#[derive(Debug,Clone)]
pub struct CNF{
    clauses: Vec<Clause>
}

#[derive(Debug,Clone)]
pub struct Clause{
    pub literals: HashSet<Literal>
}

#[derive(Clone,Debug)]
pub struct TruthAssignment{
    assignment: HashMap<i32,bool>
}

#[derive(Debug,Copy,Clone,PartialEq,Hash)]
pub enum Polarity{Positive, Negative}

impl Eq for Polarity{}

#[derive(Debug,Clone,Eq,Hash)]
pub struct Literal{
    pub variable: i32,
    pub polarity: Polarity
}

impl PartialEq for Literal{
    fn eq(&self, other: &Self)->bool{
        if self.variable==other.variable{
            if self.polarity==other.polarity{
                return true;
            }
        }
        return false;
    }
}

impl CNF{
    pub fn new()->Self{
        CNF { clauses: vec![] }
    }

    pub fn from_boolean_formula(formula: &BooleanFormula)->Self{
        formula.to_cnf_representation()
    }

    pub fn add_clause(&mut self,clause: Clause){
        self.clauses.push(clause);
    }

    pub fn is_true(&self)->bool{
        self.clauses.len()==0
    }

    pub fn is_false(&self)->bool{
        for clause in self.clauses.iter(){
            if clause.is_false(){
                return true;
            }
        }
        return false;
    }

    pub fn choose_literal(&self)->Literal{
        for clause in self.clauses.iter(){
            for literal in clause.literals.iter(){
                return literal.clone()
            }
        }
        panic!("Choosing literal from empty formula!!!");
    }

    pub fn get_pures(&self)->HashSet<Literal>{
        let mut polarity_map:HashMap<i32,Polarity>=HashMap::new();
        let mut unpure_set:HashSet<i32>=HashSet::new();
        let mut variable_set:HashSet<Literal>=HashSet::new();
        for clause in self.clauses.iter(){
            for literal in clause.literals.iter(){
                let variable_name=literal.variable;
                if polarity_map.contains_key(&variable_name){
                    if *polarity_map.get(&variable_name).unwrap()!=literal.polarity{
                        unpure_set.insert(variable_name);
                    }
                }else{
                    polarity_map.insert(variable_name,literal.polarity);
                    variable_set.insert(Literal::new(literal.polarity,variable_name));
                }
            }
        }
        for unpure in unpure_set.into_iter(){
            let unpures_polarity=*polarity_map.get(&unpure).unwrap();
            variable_set.remove(&Literal::new(unpures_polarity,unpure));
        }
        variable_set
    }

    pub fn has_pures(&self)->bool{
        !self.get_pures().is_empty()
    }

    pub fn simplify_pure_literal(&mut self,pure: &Literal){
        let mut simply_vec:Vec<usize>=vec![];
        for i in 0..self.clauses.len(){
            let clause=self.clauses.get(i).unwrap();
            if clause.contains_literal(pure){
                simply_vec.push(i);
            }
        }
        simply_vec.reverse();
        for i in simply_vec{
            self.clauses.remove(i);
        }
    }

    pub fn simplify_all_pures(&mut self){
        let mut pures=self.get_pures();
        while !pures.is_empty(){
            for pure in pures.iter(){
                self.simplify_pure_literal(&pure)
            }
            pures=self.get_pures();
        }
    }

    pub fn simplify_all_pures_and_update_assignment(&mut self,assignment: &mut TruthAssignment){
        let mut pures=self.get_pures();
        while !pures.is_empty(){
            for pure in pures.iter(){
                assignment.add_assignment_from_literal(&pure);
                self.simplify_pure_literal(&pure)
            }
            pures=self.get_pures();
        }
    }

    pub fn get_units(&self)->Vec<Literal>{
        let mut res:Vec<Literal>=vec![];
        for i in 0..self.clauses.len(){
            let clause=self.clauses.get(i).unwrap();
            if clause.is_unit(){
                for x in clause.literals.iter(){
                    res.push(x.clone());
                }
            }
        }
        return res;
    }

    pub fn has_unit(&self)->bool{
        !(self.get_units().len()==0)
    }

    pub fn simplify_unit_literal(&mut self,unit: &Literal){
        let mut simply_vec:Vec<usize>=vec![];
        for i in 0..self.clauses.len(){
            let clause=self.clauses.get_mut(i).unwrap();
            if clause.contains_variable(unit.variable){
                let not_unit=unit.not();
                if clause.literals.contains(&unit){
                    simply_vec.push(i);
                }else{
                    clause.literals.remove(&not_unit);
                }
            }
        }
        simply_vec.reverse();
        for i in simply_vec{
            self.clauses.remove(i);
        }
    }

    pub fn simplify_all_units(&mut self){
        let mut units=self.get_units();
        while !units.is_empty(){
            for unit in units.iter(){
                self.simplify_unit_literal(&unit);
            }
            units=self.get_units();
        }
    }

    pub fn simplify_all_units_and_update_assignment(&mut self, assignment:&mut TruthAssignment){
        let mut units=self.get_units();
        while !units.is_empty(){
            for unit in units.iter(){
                assignment.add_assignment_from_literal(&unit);
                self.simplify_unit_literal(&unit);
            }
            units=self.get_units();
        }
    }

    pub fn simplify_literal(&mut self,l: &Literal){
        self.simplify_unit_literal(l);
    }

    pub fn to_string(&self)->String{
        let mut res="".to_string();
        for clause in self.clauses.iter(){
            res.push_str("(");
            let clause_str=clause.to_string();
            res.push_str(&clause_str);
            res.push_str(")");
            res.push(AND_OPERATOR_SYMBOL);
        }
        res.pop();
        return res;
    }
}

impl Clause{
    pub fn new()->Self{
        Clause { literals: HashSet::new() }
    }

    pub fn add_literal(&mut self,literal: Literal){
        self.literals.insert(literal);
    }
    
    pub fn is_false(&self)->bool{
        self.literals.len()==0
    }

    pub fn contains_literal(&self,l:&Literal)->bool{
        for literal in self.literals.iter(){
            if *l==*literal{
                return true;
            }
        }
        return false;
    }

    pub fn contains_variable(&self,var:i32)->bool{
        for literal in self.literals.iter(){
            if var==literal.variable{
                return true;
            }
        }
        return false;
    }

    pub fn is_unit(&self)->bool{
        self.literals.len()==1
    }

    pub fn to_string(&self)->String{
        let mut res="".to_string();
        for literal in self.literals.iter(){
            if literal.polarity==Polarity::Negative{
                res.push(NEGATION_OPERATOR_SYMBOL)
            }
            let x=literal.variable;
            if x>=0{
                let str_var=x.to_string();
                res.push_str(&str_var);
            }else{
                let y=-x;
                res.push(FRESH_VARIABLE_SYMBOL);
                let str_var=y.to_string();
                res.push_str(&str_var);
            }
            res.push(OR_OPERATOR_SYMBOL);
        }
        res.pop();
        return res;
    }
}

impl Literal{
    pub fn new(polarity: Polarity, variable: i32)->Self{
        Literal { variable, polarity }
    }

    pub fn not(&self)->Self{
        let polarity=if self.polarity==Polarity::Positive{Polarity::Negative}else{Polarity::Positive};
        Literal { variable: self.variable, polarity }
    }
}

impl TruthAssignment{
    pub fn new()->Self{
        TruthAssignment{
            assignment: HashMap::new()
        }
    }

    pub fn add_assignment_from_literal(&mut self,l:&Literal){
        let variable=l.variable;
        match &l.polarity{
            Polarity::Positive=>{
                self.add_assignment(variable, true);
            },
            Polarity::Negative=>{
                self.add_assignment(variable, false);
            }
        }
    }

    pub fn remove_assignment_from_literal(&mut self, l: &Literal){
        let variable=l.variable;
        self.remove_assignment(variable);
    }

    pub fn add_assignment(&mut self,variable:i32,value:bool){
        self.assignment.insert(variable,value);
    }

    pub fn get_assignment(&self, variable: i32)->Option<bool>{
        self.assignment.get(&variable).copied()
    }

    pub fn remove_assignment(&mut self, variable: i32){
        self.assignment.remove(&variable);
    }

    pub fn get_assignment_or_default(&self,variable:i32)->bool{
        match self.assignment.get(&variable){
            None=>false,
            Some(b)=>*b
        }
    }
}

pub fn check_sat_dpll(formula: &BooleanFormula)->bool{
    if formula.is_true(){return true;}
    if formula.is_false(){return false;}
    let cnf=CNF::from_boolean_formula(formula);
    /*let string_of_cnf=cnf.to_string();
    println!("Checking satisfiability of equivalent formula in CNF {}",string_of_cnf);*/
    return check_sat_dpll_recursive(cnf);
}

fn check_sat_dpll_recursive(formula: CNF)->bool{
    if formula.is_true(){
        return true;
    }
    if formula.is_false(){
        return false;
    }
    if formula.has_unit(){
        let mut cloned=formula.clone();
        cloned.simplify_all_units();
        return check_sat_dpll_recursive(cloned);
    }
    if formula.has_pures(){
        let mut cloned=formula.clone();
        cloned.simplify_all_pures();
        return check_sat_dpll_recursive(cloned);
    }
    // equivalent to lazy evaluation of an Or
    // I am not doint the or directly because I am
    // worried about the formula cloning taking up memory
    let chosen=formula.choose_literal();
    let chosen_negation=chosen.not();
    let mut cloned=formula.clone();
    cloned.simplify_literal(&chosen);
    let chosen_result=check_sat_dpll_recursive(cloned);
    if chosen_result{
        return true;
    }else{
        cloned=formula.clone();
        cloned.simplify_literal(&chosen_negation);
        return check_sat_dpll_recursive(cloned);
    }
}

pub fn check_sat_dpll_and_find_assignment(formula: &BooleanFormula)->Option<TruthAssignment>{
    let assignment=TruthAssignment::new();
    if formula.is_true(){return Some(assignment);}
    if formula.is_false(){return None;}
    let cnf=CNF::from_boolean_formula(formula);
    /*let string_of_cnf=cnf.to_string();
    println!("Checking satisfiability of equivalent formula in CNF {}",string_of_cnf);*/
    match check_sat_dpll_and_find_assignment_recursive(assignment,cnf){
        Ok(assignment)=>Some(assignment),
        Err(_)=>None
    }
}

fn check_sat_dpll_and_find_assignment_recursive(mut assignment:TruthAssignment,formula: CNF)->Result<TruthAssignment,TruthAssignment>{
    if formula.is_true(){
        return Ok(assignment);
    }
    if formula.is_false(){
        return Err(assignment);
    }
    if formula.has_unit(){
        let mut cloned=formula.clone();
        cloned.simplify_all_units_and_update_assignment(&mut assignment);
        return check_sat_dpll_and_find_assignment_recursive(assignment,cloned);
    }
    if formula.has_pures(){
        let mut cloned=formula.clone();
        cloned.simplify_all_pures_and_update_assignment(&mut assignment);
        return check_sat_dpll_and_find_assignment_recursive(assignment,cloned);
    }
    let chosen=formula.choose_literal();
    let chosen_negation=chosen.not();
    let mut cloned=formula.clone();
    cloned.simplify_literal(&chosen);
    assignment.add_assignment_from_literal(&chosen);
    match check_sat_dpll_and_find_assignment_recursive(assignment,cloned){
        Ok(assignment)=>{return Ok(assignment);},
        Err(mut assignment)=>{
            assignment.remove_assignment_from_literal(&chosen);
            cloned=formula.clone();
            cloned.simplify_literal(&chosen_negation);
            assignment.add_assignment_from_literal(&chosen_negation);
            return check_sat_dpll_and_find_assignment_recursive(assignment,cloned);
        }
    }
}


fn check_validity_dpll(formula: &BooleanFormula)->bool{
    let not_formula=formula.not();
    return !check_sat_dpll(&not_formula);
}

fn check_entailment_dpll(f1: &BooleanFormula, f2: &BooleanFormula)->bool{
    let entailment=f1.entail(f2);
    return check_validity_dpll(&entailment);
}
#[allow(non_snake_case)]
#[allow(dead_code)]
mod formula;
mod sat;

fn main() {
    let f=formula::BooleanFormula::new_default();
    println!("Default: {:?}",f);
    let string="(1*2)+(-1*2)+(-2*1)+(-1*-2)".to_string();
    let parsed=formula::BooleanFormula::from_string(string);
    println!("Parsed from string: {}",parsed.to_string());
    let parsed_from_str=formula::BooleanFormula::from_str("((1=2)=(3=4))+1+-(-2*3*-1)+(1=2)");
    println!("Parsed from str: {}",parsed_from_str.to_string());
    let parsed_nnf=parsed.get_nnf();
    println!("NNF: {}",parsed_nnf.to_string());
    let parsed_cnf=parsed.get_cnf();
    println!("CNF: {}",parsed_cnf.to_string());
    let parsed_without_quantifiers=parsed.without_quantifiers();
    println!("Without Quantifiers: {}",parsed_without_quantifiers.to_string());
    let sat=sat::check_sat_dpll(&parsed);
    if sat{
        println!("{} is satisfiable",parsed.to_string());
    }else{
        println!("{} is unsatisfiable",parsed.to_string());
    }
}

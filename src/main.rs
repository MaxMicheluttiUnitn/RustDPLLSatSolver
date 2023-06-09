//#![allow(non_snake_case)]
#![allow(dead_code)]
mod formula;
mod sat;
mod operators;

fn main() {
    //let string="-((1+2)=-(2*3))".to_string();
    let string="A1.2+-f1".to_string();
    let parsed=match formula::BooleanFormula::from_string(string){
        Ok(formula)=>formula,
        Err(s)=>{
            println!("Got the following error: {}",s);
            std::process::exit(1);
        }
    };
    println!("Parsed from string: {}",parsed);
    let str="T*(T+((-10=E10.20)=(0=4))+1+-(-2*3*-1)+(1=2)+F+0)*12";
    let parsed_from_str=match formula::BooleanFormula::from_str(str){
        Ok(formula)=>formula,
        Err(s)=>{
            println!("Got the following error: {}",s);
            std::process::exit(1);
        }
    };
    println!("Parsed from str: {}",parsed_from_str);
    let parsed_nnf=parsed.get_nnf();
    println!("NNF: {}",parsed_nnf);
    let parsed_cnf=parsed.get_cnf();
    println!("CNF: {}",parsed_cnf);
    let cloned=parsed.clone();
    println!("Cloned: {}",cloned);
    let parsed_without_quantifiers=parsed.without_quantifiers();
    println!("Without Quantifiers: {}",parsed_without_quantifiers);
    /*let sat=sat::check_sat_dpll(&parsed);
    if sat{
        println!("{} is satisfiable",parsed.to_string());
    }else{
        println!("{} is unsatisfiable",parsed.to_string());
    }*/
    let sat_assigned=sat::check_sat_dpll_and_find_assignment(&parsed);
    match sat_assigned{
        Some(assignment)=>{
            println!("{} is satisfiable",parsed);
            let variables=parsed_cnf.get_variables();
            println!("Assignment:");
            for var in variables{
                let assign=assignment.get_assignment_or_default(*var);
                if assign{
                    println!("{}: true",var);
                }else{
                    println!("{}: false",var);
                }
            }
        },
        None=>{println!("{} is unsatisfiable",parsed);}
    }
}

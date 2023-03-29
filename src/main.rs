//#![allow(non_snake_case)]
#![allow(dead_code)]
mod formula;
mod sat;

fn main() {
    //let string="-((1+2)=-(2*3))".to_string();
    let string="T+((-10=E10.20)=(0=4))+1+-(-2*3*-1)+(1=2)+0".to_string();
    let parsed=match formula::BooleanFormula::from_string(string){
        Ok(formula)=>formula,
        Err(s)=>{
            println!("Got the following error: {}",s);
            std::process::exit(1);
        }
    };
    println!("Parsed from string: {}",parsed.to_string());
    let str="T+((-10=E10.20)=(0=4))+1+-(-2*3*-1)+(1=2)+F+0";
    let parsed_from_str=match formula::BooleanFormula::from_str(str){
        Ok(formula)=>formula,
        Err(s)=>{
            println!("Got the following error: {}",s);
            std::process::exit(1);
        }
    };
    println!("Parsed from str: {}",parsed_from_str.to_string());
    let parsed_nnf=parsed.get_nnf();
    println!("NNF: {}",parsed_nnf.to_string());
    let parsed_cnf=parsed.get_cnf();
    println!("CNF: {}",parsed_cnf.to_string());
    let cloned_cnf=parsed_cnf.clone();
    println!("Cloned CNF: {}",cloned_cnf.to_string());
    let parsed_without_quantifiers=parsed.without_quantifiers();
    println!("Without Quantifiers: {}",parsed_without_quantifiers.to_string());
    /*let sat=sat::check_sat_dpll(&parsed);
    if sat{
        println!("{} is satisfiable",parsed.to_string());
    }else{
        println!("{} is unsatisfiable",parsed.to_string());
    }*/
    let sat_assigned=sat::check_sat_dpll_and_find_assignment(&parsed);
    match sat_assigned{
        Some(assignment)=>{
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
        None=>{println!("{} is unsatisfiable",parsed.to_string());}
    }
}

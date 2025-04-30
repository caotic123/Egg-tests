use egg::*;

define_language! {
    enum Rare {
        Num(i32),
        "~" = Eq([Id; 2]),
        "App" = App(Vec<Id>),
        "Func" = Func([Id; 2]),
        "Var" = Var(Id),
        "Sort" = Sort(Id),
        "List" = List(Vec<Id>),
        "Op" = Op(Vec<Id>),
        "Appl" = Appl([Id; 2]),
        Symbol(String),
    }
}

fn make_rules() -> Vec<Rewrite<Rare, ()>> {
    vec![
        rewrite!("func_apply"; "(Func Top (~ ?x ?y))" => "Top"),
        rewrite!("reduction1"; "(Func Top (~ ?x ?y))" => " (~ ?x ?y)"),
     //  rewrite!("reduction2"; "(Func Top (~ ?x ?y))" => "?x"),
    //   rewrite!("reduction3"; "(Func Top (~ ?x ?y))" => "?y"),

       // rewrite!("func_recu"; "?x" => "(Func ?x ?x)"),
        rewrite!("eq_trans_reduction"; "(Appl ?y (~ ?x ?z))" 
           => "(Func (~ ?x ?y) (Func (~ ?y ?z) (~ ?x ?z))))))"),
       rewrite!("ignore"; "(~ ?x ?z)" => "(Appl Bool (~ ?x ?z))"),

        //rewrite!("eq_sym_reduction2"; "(~ ?x ?y)" => "(Func (~ ?x true) (Func (~ ?y false) (~ true false)))"),

    //    rewrite!("eq_sym_ground"; "(Func (~ ?x ?y) (~ ?y ?x))" => "Top"),
        rewrite!("base1"; "(~ t1 t2)" => "Top"),
        rewrite!("base2"; "(~ t2 t3)" => "Top"),
       // rewrite!("type1"; "Bool" => "t1"),
        rewrite!("type2"; "Bool" => "t2"),
      //  rewrite!("type3"; "Bool" => "t3"),

    ]
}

/// parse an expression, simplify it using egg, and pretty print it back out
fn simplify(head: &str, s: Vec<&str>) -> String {
    let mut runner = Runner::default();
    let head: RecExpr<Rare> = head.parse().unwrap();
    runner = runner.with_explanations_enabled().with_expr(&head);

    // parse the expression, the type annotation tells it which Language to use
    for str in s {
        let expr: RecExpr<Rare> = str.parse().unwrap();
        runner = runner.with_expr(&expr);
        println!("test {0}", expr);
    }

    runner = runner.run(&make_rules());

    // simplify the expression using a Runner, which creates an e-graph with
    // the given expression and runs the given rules over it
    // the Runner knows which e-class the expression given with `with_expr` is in
    let root = runner.roots[0];

    // use an Extractor to pick the best element of the root eclass
    let extractor = Extractor::new(&runner.egraph, AstSize);
    let (best_cost, best) = extractor.find_best(root);
    println!("Simplified {} to {} with cost {} to {}", head, best, best_cost, runner.explain_equivalence(&head, &best));
    best.to_string()
}

fn main() {
    println!("{0}", simplify("(~ t1 t3)", vec![]));
}

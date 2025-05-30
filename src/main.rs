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
        "Inst" = Inst(Vec<Id>),
        "Ground" = Ground(Id),
        "Inhabitant" = Inhabitant(Vec<Id>),
        "Mk" = Mk([Id; 1]),
        Symbol(String),
    }
}

fn make_rules() -> Vec<Rewrite<Rare, ()>> {
    vec![
        rewrite!("func_dependency"; "(Func ?v (~ ?x ?y))" => "(Func (Mk ?v) (~ ?x ?y))"),
        rewrite!("func_Insty"; "(Func Top (~ ?x ?y))" => "Top"),
        rewrite!("func_Insty2"; "(Func (Func Top (~ ?a ?b)) (~ ?c ?d))" => "(Func (~ ?a ?b) (~ ?c ?d))"),
        // rewrite!("reduction2"; "(Func Top (~ ?x ?y))" => "?x"),
        // rewrite!("reduction3"; "(Func Top (~ ?x ?y))" => "?y"),

        //   rewrite!("func_recu"; "?x" => "(Func ?x ?x)"),
        rewrite!("eq_trans_reduction"; "(Inst (Inhabitant Free Bool ?y) (Inhabitant Ground Bool ?x) (Inhabitant Ground Bool ?z)))" 
       => "(Func (~ ?x ?y) (Func (~ ?y ?z) (~ ?x ?z))))))"),
        rewrite!("ignore"; "(Mk (~ ?x ?z))" => "(Inst any (Ground ?x) (Ground ?z))"),
        rewrite!("goal_test"; "(Inst eq_trans (Inhabitant Ground Bool ?x))" 
       => "(Func (~ t1 t3) (~ ?x goal))"),
        rewrite!("ignore2"; "(Mk (~ ?x goal))" => "(Inst eq_trans (Ground ?x))"),
        rewrite!("eq_refl"; "(Inst eq_refl (Inhabitant Ground ?p ?x))" 
       => "(Func Top (~ ?x ?x))"),
        rewrite!("inst_eq_refl"; "(Mk (~ ?x ?x))" => "(Inst eq_refl (Ground ?x))"),

        rewrite!("not_rule"; "(Ground (App (Op not) ?t))" => "(Inhabitant Ground Bool (App (Op not) ?t))"),

        //rewrite!("eq_sym_reduction2"; "(~ ?x ?y)" => "(Func (~ ?x true) (Func (~ ?y false) (~ true false)))"),

        //    rewrite!("eq_sym_ground"; "(Func (~ ?x ?y) (~ ?y ?x))" => "Top"),
        rewrite!("base1"; "(~ t1 t2)" => "Top"),
        rewrite!("base2"; "(~ t2 t3)" => "Top"),
        rewrite!("t1"; "(Ground t1)" => "(Inhabitant Ground Bool t1)"),
        rewrite!("t2"; "(Ground t2)" => "(Inhabitant Ground Bool t2)"),
        rewrite!("t3"; "(Ground t3)" => "(Inhabitant Ground Bool t3)"),
        rewrite!("type1"; "any" => "(Inhabitant Free Bool t1)"),
        rewrite!("type2"; "any" => "(Inhabitant Free Bool t2)"),
        rewrite!("type3"; "any" => "(Inhabitant Free Bool t3)"),
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

    // runner.egraph.explain_equivalence(
    //     &"(Inhabitant Bool t1)".parse().unwrap(),
    //     &"(Inhabitant Bool t3)".parse().unwrap(),
    // );


    // simplify the expression using a Runner, which creates an e-graph with
    // the given expression and runs the given rules over it
    // the Runner knows which e-class the expression given with `with_expr` is in
    let root = runner.roots[0];

    // use an Extractor to pick the best element of the root eclass
    let extractor = Extractor::new(&runner.egraph, AstSize);
    let (best_cost, best) = extractor.find_best(root);
    println!(
        "Simplified {} to {} with cost {} to {}",
        head,
        best,
        best_cost,
        runner.explain_equivalence(&head, &best)
    );
    best.to_string()
}

fn main() {
    println!("{0}", simplify("(Mk (~ (App (Op not) t1) goal))", vec![]));
}

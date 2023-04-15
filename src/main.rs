use std::default;

use ArithCmpOp::*;
use ArithExpr::*;
use BinArithOp::*;
use BinLogicOp::*;
use BoolExpr::*;
use Expr::*;
use Value::*;

pub enum Expr {
    ArithExpr(ArithExpr),
    BoolExpr(BoolExpr),
}

pub enum ArithExpr {
    BinArithExpr {
        left: Box<ArithExpr>,
        right: Box<ArithExpr>,
        op: BinArithOp,
    },
    IntLit(i64),
}

pub enum BoolExpr {
    ArithCmpExpr {
        left: Box<ArithExpr>,
        right: Box<ArithExpr>,
        op: ArithCmpOp,
    },
    BinBoolExpr {
        left: Box<BoolExpr>,
        right: Box<BoolExpr>,
        op: BinLogicOp,
    },
    NotExpr(Box<BoolExpr>),
    BoolLit(bool),
}

pub enum BinArithOp {
    AddOp,
    SubOp,
    MulOp,
    IntDivOp,
}

pub enum ArithCmpOp {
    LtOp,
    LteOp,
    GtOp,
    GteOp,
    ArithEqOp,
    ArithNeqOp,
}

pub enum BinLogicOp {
    AndOp,
    OrOp,
    BoolEqOp,
    BoolNeqOp,
}

#[derive(Debug, PartialEq)]
pub enum Value {
    BoolValue(bool),
    IntValue(i64),
}

pub fn eval(expr: Expr) -> Value {
    match expr {
        ArithExpr(expr) => IntValue(eval_arith_expr(expr)),
        BoolExpr(expr) => BoolValue(eval_bool_expr(expr)),
    }
}

pub fn eval_arith_expr(arith_expr: ArithExpr) -> i64 {
    match arith_expr {
        BinArithExpr { left, right, op } => match op {
            AddOp => eval_arith_expr(*left) + eval_arith_expr(*right),
            SubOp => eval_arith_expr(*left) - eval_arith_expr(*right),
            MulOp => eval_arith_expr(*left) * eval_arith_expr(*right),
            IntDivOp => eval_arith_expr(*left) / eval_arith_expr(*right),
        },
        IntLit(num) => num,
    }
}

pub fn eval_bool_expr(bool_expr: BoolExpr) -> bool {
    match bool_expr {
        ArithCmpExpr { left, right, op } => match op {
            LtOp => eval_arith_expr(*left) < eval_arith_expr(*right),
            LteOp => eval_arith_expr(*left) <= eval_arith_expr(*right),
            GtOp => eval_arith_expr(*left) > eval_arith_expr(*right),
            GteOp => eval_arith_expr(*left) >= eval_arith_expr(*right),
            ArithEqOp => eval_arith_expr(*left) == eval_arith_expr(*right),
            ArithNeqOp => eval_arith_expr(*left) != eval_arith_expr(*right),
        },
        BinBoolExpr { left, right, op } => match op {
            AndOp => eval_bool_expr(*left) && eval_bool_expr(*right),
            OrOp => eval_bool_expr(*left) || eval_bool_expr(*right),
            BoolEqOp => eval_bool_expr(*left) == eval_bool_expr(*right),
            BoolNeqOp => eval_bool_expr(*left) != eval_bool_expr(*right),
        },
        NotExpr(expr) => !eval_bool_expr(*expr),
        BoolLit(bool) => bool,
    }
}

fn main() {}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn test_sample() {
        let expr = BoolExpr(BoolLit(true));
        let answer = BoolValue(true);
        assert_eq!(eval(expr), answer); // eval(BoolExpr(BoolLit(true))) == BoolValue(true)
    }

    // Arithmetic Operations
    #[test]
    fn test_add() {
        assert_eq!(
            eval(ArithExpr(BinArithExpr {
                left: Box::new(IntLit(10)),
                right: Box::new(IntLit(20)),
                op: AddOp
            })),
            IntValue(30)
        )
    }

    #[test]
    fn test_sub() {
        assert_eq!(
            eval(ArithExpr(BinArithExpr {
                left: Box::new(IntLit(20)),
                right: Box::new(IntLit(40)),
                op: SubOp
            })),
            IntValue(-20)
        )
    }

    #[test]
    fn test_mult() {
        assert_eq!(
            eval(ArithExpr(BinArithExpr {
                left: Box::new(IntLit(4)),
                right: Box::new(IntLit(2)),
                op: MulOp
            })),
            IntValue(8)
        )
    }

    #[test]
    fn test_div() {
        assert_eq!(
            eval(ArithExpr(BinArithExpr {
                left: Box::new(IntLit(10)),
                right: Box::new(IntLit(2)),
                op: IntDivOp
            })),
            IntValue(5)
        )
    }

    // Binary Operations
    #[test]
    fn test_less_than() {
        assert_eq!(
            eval(BoolExpr(ArithCmpExpr {
                left: Box::new(IntLit(5)),
                right: Box::new(IntLit(10)),
                op: LtOp
            })),
            BoolValue(true)
        )
    }

    #[test]
    fn test_less_eq_than() {
        assert_eq!(
            eval(BoolExpr(ArithCmpExpr {
                left: Box::new(IntLit(10)),
                right: Box::new(IntLit(10)),
                op: LteOp
            })),
            BoolValue(true)
        )
    }

    #[test]
    fn test_greater_than() {
        assert_eq!(
            eval(BoolExpr(ArithCmpExpr {
                left: Box::new(IntLit(15)),
                right: Box::new(IntLit(10)),
                op: GtOp
            })),
            BoolValue(true)
        )
    }

    #[test]
    fn test_greater_eq_than() {
        assert_eq!(
            eval(BoolExpr(ArithCmpExpr {
                left: Box::new(IntLit(15)),
                right: Box::new(IntLit(10)),
                op: GteOp
            })),
            BoolValue(true)
        )
    }

    #[test]
    fn test_arith_eq_than() {
        assert_eq!(
            eval(BoolExpr(ArithCmpExpr {
                left: Box::new(IntLit(10)),
                right: Box::new(IntLit(10)),
                op: ArithEqOp
            })),
            BoolValue(true)
        )
    }

    #[test]
    fn test_arith_neq_than() {
        assert_eq!(
            eval(BoolExpr(ArithCmpExpr {
                left: Box::new(IntLit(25)),
                right: Box::new(IntLit(10)),
                op: ArithNeqOp
            })),
            BoolValue(true)
        )
    }

    #[test]
    fn test_bin_and() {
        assert_eq!(
            eval(BoolExpr(BinBoolExpr {
                left: Box::new(BoolLit(true)),
                right: Box::new(BoolLit(false)),
                op: AndOp
            })),
            BoolValue(false)
        )
    }

    #[test]
    fn test_bin_or() {
        assert_eq!(
            eval(BoolExpr(BinBoolExpr {
                left: Box::new(BoolLit(true)),
                right: Box::new(BoolLit(false)),
                op: OrOp
            })),
            BoolValue(true)
        )
    }

    #[test]
    fn test_bin_eq() {
        assert_eq!(
            eval(BoolExpr(BinBoolExpr {
                left: Box::new(BoolLit(true)),
                right: Box::new(BoolLit(false)),
                op: BoolEqOp
            })),
            BoolValue(false)
        )
    }

    #[test]
    fn test_bin_neq() {
        assert_eq!(
            eval(BoolExpr(BinBoolExpr {
                left: Box::new(BoolLit(true)),
                right: Box::new(BoolLit(false)),
                op: BoolNeqOp
            })),
            BoolValue(true)
        )
    }

    #[test]
    fn test_bin_not() {
        assert_eq!(
            eval(BoolExpr(NotExpr(Box::new(BoolLit(true))))),
            BoolValue(false)
        )
    }

    #[test]
    fn test_others() {
        main();
        println!("{:?}", BoolValue(true));
    }
}

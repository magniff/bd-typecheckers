// Based on David Christiansen's tutorial https://davidchristiansen.dk/tutorials/bidirectional.pdf
#![allow(dead_code)]

#[derive(Debug)]
enum Expression {
    Variable(String),
    Application(Box<Expression>, Box<Expression>),
    Abstraction(String, Box<Expression>),
    Condition {
        cond: Box<Expression>,
        true_branch: Box<Expression>,
        false_branch: Box<Expression>,
    },
    Annotation {
        expression: Box<Expression>,
        with: Type,
    },
    True,
    False,
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum Type {
    Bool,
    Function(Box<Type>, Box<Type>),
}

impl std::fmt::Display for Expression {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Expression::Variable(varname) => {
                write!(f, "{varname}")
            }
            Expression::Application(caller, callee) => {
                write!(f, "{caller}({callee})")
            }
            Expression::Abstraction(varname, callee) => {
                write!(f, "\\λ ({varname}) . {{ {callee} }}")
            }
            #[allow(non_snake_case)]
            Expression::Condition {
                cond,
                true_branch,
                false_branch,
            } => {
                write!(f, "if ({cond}) then {true_branch} else {false_branch}")
            }
            Expression::Annotation {
                expression: e,
                with: t,
            } => {
                write!(f, "{e}: {t}")
            }
            Expression::True => {
                write!(f, "true")
            }
            Expression::False => {
                write!(f, "false")
            }
        }
    }
}

impl std::fmt::Display for Type {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Type::Bool => {
                write!(f, "Bool")
            }
            Type::Function(from, to) => {
                write!(f, "{from} -> {to}")
            }
        }
    }
}

type Gamma = std::collections::HashMap<String, Type>;

fn check_type<'a>(gamma: &Gamma, expr: &Expression, type_expected: &Type) -> bool {
    match expr {
        Expression::Condition {
            cond,
            true_branch: t,
            false_branch: f,
        } => {
            check_type(gamma, cond, &Type::Bool)
                && check_type(gamma, t, type_expected)
                && check_type(gamma, f, type_expected)
        }
        Expression::Abstraction(varname, body) => match type_expected {
            Type::Function(from, to) => {
                let mut fresh_gamma = gamma.clone();
                fresh_gamma.insert(varname.clone(), from.as_ref().clone());
                check_type(&fresh_gamma, body, to)
            }
            _ => false,
        },
        _ => infer_type(gamma, expr).as_ref() == Some(type_expected),
    }
}

fn infer_type(gamma: &Gamma, expr: &Expression) -> Option<Type> {
    match expr {
        Expression::Variable(varname) => gamma.get(varname).cloned(),
        Expression::True | Expression::False => Some(Type::Bool),
        Expression::Annotation {
            expression: e,
            with: t,
        } => {
            if check_type(gamma, e, t) {
                Some(t.clone())
            } else {
                None
            }
        }
        Expression::Application(func, callee) => infer_type(gamma, func)
            .and_then(|function_type| match function_type {
                Type::Function(from_type, to_type) => {
                    if check_type(gamma, callee, &from_type) {
                        Some(to_type)
                    } else {
                        None
                    }
                }
                _ => None,
            })
            .as_deref()
            .cloned(),
        Expression::Abstraction(..) | Expression::Condition { .. } => None,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::HashMap;

    fn empty_ctx() -> Gamma {
        HashMap::new()
    }

    fn bool_type() -> Type {
        Type::Bool
    }

    fn fn_type(a: Type, b: Type) -> Type {
        Type::Function(Box::new(a), Box::new(b))
    }

    fn var(name: &str) -> Expression {
        Expression::Variable(name.to_string())
    }

    fn abs(name: &str, body: Expression) -> Expression {
        Expression::Abstraction(name.to_string(), Box::new(body))
    }

    fn app(f: Expression, x: Expression) -> Expression {
        Expression::Application(Box::new(f), Box::new(x))
    }

    fn annot(e: Expression, t: Type) -> Expression {
        Expression::Annotation {
            expression: Box::new(e),
            with: t,
        }
    }

    fn cond(c: Expression, t: Expression, f: Expression) -> Expression {
        Expression::Condition {
            cond: Box::new(c),
            true_branch: Box::new(t),
            false_branch: Box::new(f),
        }
    }

    // ------------------------------------------------------------
    // Basic literals
    // ------------------------------------------------------------
    #[test]
    fn infer_true_false() {
        assert_eq!(
            infer_type(&empty_ctx(), &Expression::True),
            Some(bool_type())
        );
        assert_eq!(
            infer_type(&empty_ctx(), &Expression::False),
            Some(bool_type())
        );
    }

    // ------------------------------------------------------------
    // Variables
    // ------------------------------------------------------------
    #[test]
    fn infer_variable() {
        let mut ctx = empty_ctx();
        ctx.insert("x".into(), bool_type());
        assert_eq!(infer_type(&ctx, &var("x")), Some(bool_type()));
    }

    #[test]
    fn unknown_variable_fails() {
        assert_eq!(infer_type(&empty_ctx(), &var("x")), None);
    }

    // ------------------------------------------------------------
    // Simple lambda
    // ------------------------------------------------------------
    #[test]
    fn check_identity_lambda() {
        let id = abs("x", var("x"));
        let ty = fn_type(bool_type(), bool_type());
        assert!(check_type(&empty_ctx(), &id, &ty));
    }

    #[test]
    fn lambda_wrong_expected_type() {
        let id = abs("x", var("x"));
        assert!(!check_type(&empty_ctx(), &id, &bool_type()));
    }

    #[test]
    fn cannot_infer_lambda_without_annotation() {
        let id = abs("x", var("x"));
        assert_eq!(infer_type(&empty_ctx(), &id), None);
    }

    // ------------------------------------------------------------
    // Application
    // ------------------------------------------------------------
    #[test]
    fn infer_simple_application() {
        let id = annot(abs("x", var("x")), fn_type(bool_type(), bool_type()));
        let expr = app(id, Expression::True);
        assert_eq!(infer_type(&empty_ctx(), &expr), Some(bool_type()));
    }

    #[test]
    fn application_argument_type_mismatch() {
        let id = annot(abs("x", var("x")), fn_type(bool_type(), bool_type()));
        let expr = app(id, abs("y", var("y"))); // lambda instead of bool
        assert_eq!(infer_type(&empty_ctx(), &expr), None);
    }

    #[test]
    fn application_of_non_function_fails() {
        let expr = app(Expression::True, Expression::True);
        assert_eq!(infer_type(&empty_ctx(), &expr), None);
    }

    // ------------------------------------------------------------
    // Conditionals
    // ------------------------------------------------------------
    #[test]
    fn check_simple_conditional() {
        let expr = cond(Expression::True, Expression::True, Expression::False);
        assert!(check_type(&empty_ctx(), &expr, &bool_type()));
    }

    #[test]
    fn conditional_requires_bool_condition() {
        let bad = cond(abs("x", var("x")), Expression::True, Expression::False);
        assert!(!check_type(&empty_ctx(), &bad, &bool_type()));
    }

    #[test]
    fn conditional_branch_mismatch() {
        let good = cond(Expression::True, Expression::True, Expression::False);
        let fn_ty = fn_type(bool_type(), bool_type());
        assert!(!check_type(&empty_ctx(), &good, &fn_ty));
    }

    // ------------------------------------------------------------
    // Annotations
    // ------------------------------------------------------------
    #[test]
    fn annotation_success() {
        let id = abs("x", var("x"));
        let ty = fn_type(bool_type(), bool_type());
        let annotated = annot(id, ty.clone());
        assert_eq!(infer_type(&empty_ctx(), &annotated), Some(ty));
    }

    #[test]
    fn annotation_failure() {
        let id = abs("x", var("x"));
        let wrong_ty = bool_type();
        let annotated = annot(id, wrong_ty);
        assert_eq!(infer_type(&empty_ctx(), &annotated), None);
    }

    // ------------------------------------------------------------
    // Higher-order functions
    // ------------------------------------------------------------
    #[test]
    fn check_higher_order_function() {
        // λf. f true
        let expr = abs("f", app(var("f"), Expression::True));
        let ty = fn_type(fn_type(bool_type(), bool_type()), bool_type());
        assert!(check_type(&empty_ctx(), &expr, &ty));
    }

    #[test]
    fn nested_lambda() {
        // λx. λy. x
        let expr = abs("x", abs("y", var("x")));
        let ty = fn_type(bool_type(), fn_type(bool_type(), bool_type()));
        assert!(check_type(&empty_ctx(), &expr, &ty));
    }

    // ------------------------------------------------------------
    // Shadowing
    // ------------------------------------------------------------
    #[test]
    fn variable_shadowing() {
        let mut ctx = empty_ctx();
        ctx.insert("x".into(), bool_type());
        let expr = abs("x", var("x")); // inner x shadows outer
        let ty = fn_type(bool_type(), bool_type());
        assert!(check_type(&ctx, &expr, &ty));
    }

    // ------------------------------------------------------------
    // Deep ill-typed case
    // ------------------------------------------------------------
    #[test]
    fn deeply_ill_typed_program() {
        // (λx:Bool. x) (λy. y)
        let id_bool = annot(abs("x", var("x")), fn_type(bool_type(), bool_type()));
        let bad_arg = abs("y", var("y"));
        let expr = app(id_bool, bad_arg);
        assert_eq!(infer_type(&empty_ctx(), &expr), None);
    }
}

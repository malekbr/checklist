use std::collections::{btree_map, BTreeMap};
use std::iter::Peekable;

use pest::Parser;

#[derive(Parser)]
#[grammar = "../parser/template.pest"]
pub struct TemplateParser;

pub enum DataPoint {
    Primitive(String),
    List(Vec<DataPoint>),
    Object(BTreeMap<String, DataPoint>),
}

impl DataPoint {
    fn expect_primitive(&self) -> Option<&String> {
        match self {
            DataPoint::Primitive(string) => Some(string),
            _ => None,
        }
    }
    fn expect_list(&self) -> Option<&Vec<DataPoint>> {
        match self {
            DataPoint::List(data_points) => Some(data_points),
            _ => None,
        }
    }
    fn expect_object(&self) -> Option<&BTreeMap<String, DataPoint>> {
        match self {
            DataPoint::Object(mapping) => Some(mapping),
            _ => None,
        }
    }
}

#[derive(Clone)]
pub enum Fillable {
    Primitive,
    List(Box<Fillable>),
    Object(BTreeMap<String, Fillable>),
}

#[derive(Clone)]
enum PathPart {
    Index(usize),
    Element(String),
}

#[derive(Clone)]
struct Path(Vec<PathPart>);

impl Path {
    fn push(&self, part: PathPart) -> Self {
        let mut result = self.clone();
        result.0.push(part);
        result
    }

    fn new() -> Self {
        Path(vec![])
    }
}

pub enum ErrorType {
    Missing(Path),
    Extra(Path),
    Invalid(Path, Fillable),
}

enum DiffResult<'a, K, V1, V2> {
    Left(&'a K, &'a V1),
    Right(&'a K, &'a V2),
    Both(&'a K, &'a V1, &'a V2),
}

struct Diff<'a, K, V1, V2> {
    left: Peekable<btree_map::Iter<'a, K, V1>>,
    right: Peekable<btree_map::Iter<'a, K, V2>>,
}

impl<'a, K, V1, V2> Diff<'a, K, V1, V2> {
    fn diff(left: &'a BTreeMap<K, V1>, right: &'a BTreeMap<K, V2>) -> Self {
        Diff {
            left: left.iter().peekable(),
            right: right.iter().peekable(),
        }
    }
}

impl<'a, K: PartialEq, V1, V2> Iterator for Diff<'a, K, V1, V2> {
    type Item = DiffResult<'a, K, V1, V2>;

    fn next(&mut self) -> Option<Self::Item> {
        let lp = self.left.peek().is_some();
        let rp = self.right.peek().is_some();
        match (lp, rp) {
            (false, false) => None,
            (true, false) => {
                let (k, v) = self.left.next().unwrap();
                Some(DiffResult::Left(k, v))
            }
            (false, true) => {
                let (k, v) = self.right.next().unwrap();
                Some(DiffResult::Right(k, v))
            }
            (true, true) => {
                let (kl, vl) = self.left.next().unwrap();
                let (kr, _) = self.right.peek().unwrap();
                if kl == *kr {
                    let (_, vr) = self.right.next().unwrap();
                    Some(DiffResult::Both(kl, vl, vr))
                } else {
                    Some(DiffResult::Left(kl, vl))
                }
            }
        }
    }
}

fn verify_with_path(path: Path, data_point: &DataPoint, fillable: &Fillable) -> Vec<ErrorType> {
    match fillable {
        Fillable::Primitive => {
            if data_point.expect_primitive().is_some() {
                vec![]
            } else {
                vec![ErrorType::Invalid(path, fillable.clone())]
            }
        }
        Fillable::List(fillables) => match data_point.expect_list() {
            Some(data_points) => data_points
                .into_iter()
                .enumerate()
                .flat_map(|(i, data_point)| {
                    verify_with_path(path.push(PathPart::Index(i)), data_point, fillables)
                })
                .collect(),
            None => vec![ErrorType::Invalid(path, fillable.clone())],
        },
        Fillable::Object(mapping) => match data_point.expect_object() {
            Some(data_point_mapping) => Diff::diff(mapping, data_point_mapping)
                .flat_map(|diffresult| match diffresult {
                    DiffResult::Left(key, _) => vec![ErrorType::Missing(
                        path.push(PathPart::Element(key.clone())),
                    )],
                    DiffResult::Right(key, _) => {
                        vec![ErrorType::Extra(path.push(PathPart::Element(key.clone())))]
                    }
                    DiffResult::Both(key, fillable, data_point) => verify_with_path(
                        path.push(PathPart::Element(key.clone())),
                        data_point,
                        fillable,
                    ),
                })
                .collect(),
            None => vec![ErrorType::Invalid(path, fillable.clone())],
        },
    }
}

pub fn verify(data_point: &DataPoint, fillable: &Fillable) -> Vec<ErrorType> {
    verify_with_path(Path::new(), data_point, fillable)
}

enum TemplatePathPart {
    Index,
    Element(String),
}

struct TemplatePath(Vec<TemplatePathPart>);

#[derive(PartialEq, Debug)]
pub struct ObjectAccess(Vec<String>);

impl ObjectAccess {
    pub fn parse(string: &str) -> Result<Self, pest::error::Error<Rule>> {
        let mut result = TemplateParser::parse(Rule::group_name, string)?;
        Ok(ObjectAccess(
            result
                .next()
                .unwrap()
                .into_inner()
                .map(|pair| match pair.as_rule() {
                    Rule::ident => String::from(pair.as_str()),
                    rule => panic!("Bug in grammar, object access {:?}", rule),
                })
                .collect(),
        ))
    }
}

enum TodoLinePart {
    Const(String),
    Path(TemplatePath),
}

struct TodoLine(Vec<TodoLinePart>);

enum TodoTemplate {
    Line(TodoLine),
    Comment(TodoLine),
    Loop(String, ObjectAccess, Vec<TodoTemplate>),
}

enum Lines {
    Line(TodoLine),
    Comment(TodoLine),
    Loop(String, ObjectAccess, Vec<TodoTemplate>),
}

pub struct Template {
    templates: Vec<TodoTemplate>,
    fillables: BTreeMap<String, Fillable>,
}

struct WithIndentation<T> {
    indentation: String,
    body: T,
}

impl<T> WithIndentation<T> {
    fn new(indentation: &str, body: T) -> Self {
        WithIndentation {
            indentation: indentation.to_owned(),
            body,
        }
    }
}

fn compute_indent_str(indentation: &str) -> usize {
    indentation.chars().fold(0, |i, char| match char {
        ' ' => i + 1,
        '\t' => {
            let next = i + 8;
            next - (next % 8)
        }
        _ => panic!("Unexpected character in indentation {}", char),
    })
}

fn compute_indent(indentation: &pest::iterators::Pair<Rule>) -> usize {
    match indentation.as_rule() {
        Rule::indentation => (),
        rule => panic!("compute_indent got a non indentation: {:?}", rule),
    }
    compute_indent_str(indentation.as_str())
}

type Pair = String;

#[derive(Debug)]
enum Indentation {
    MoreThan(Pair, usize),
    Exactly(Pair, usize),
    TopLevel,
}

#[derive(Debug)]
enum Either<A, B> {
    Left(A),
    Right(B),
}

// TODO: rewrite
#[derive(Debug)]
struct Structured {
    indentation: Indentation,
    children: Vec<Either<Pair, Box<Structured>>>,
}

impl Structured {
    fn collapse(
        values: &mut Vec<Self>,
        pos: pest::Position,
    ) -> Result<(), pest::error::Error<Rule>> {
        let latest = values.last_mut().unwrap();
        match &latest.indentation {
            Indentation::TopLevel => (),
            Indentation::MoreThan(_, _) => {
                let error = pest::error::Error::new_from_pos(
                    pest::error::ErrorVariant::CustomError {
                        message: String::from("Empty loop"),
                    },
                    pos,
                );
                return Err(error);
            }
            Indentation::Exactly(_, _) => {
                let latest = values.pop().unwrap();
                values
                    .last_mut()
                    .unwrap()
                    .children
                    .push(Either::Right(Box::new(latest)));
                return Structured::collapse(values, pos);
            }
        };
        Ok(())
    }
    fn update_indent(
        values: &mut Vec<Self>,
        element: &pest::iterators::Pair<Rule>,
        indent: usize,
    ) -> Result<(), pest::error::Error<Rule>> {
        let latest = values.last_mut().unwrap();
        let error = pest::error::Error::new_from_pos(
            pest::error::ErrorVariant::CustomError {
                message: String::from("Unexpected indentation"),
            },
            element.as_span().start_pos(),
        );
        match &latest.indentation {
            Indentation::TopLevel => {
                if indent > 0 {
                    return Err(error);
                }
            }
            Indentation::MoreThan(pair, size) => {
                if indent > *size {
                    latest.indentation = Indentation::Exactly(pair.to_owned(), indent);
                } else {
                    return Err(error);
                }
            }
            Indentation::Exactly(_, size) => {
                if indent < *size {
                    let latest = values.pop().unwrap();
                    values
                        .last_mut()
                        .unwrap()
                        .children
                        .push(Either::Right(Box::new(latest)));
                    return Structured::update_indent(values, element, indent);
                } else if indent > *size {
                    return Err(error);
                }
            }
        };
        Ok(())
    }
    fn update_indent_loop_spec(
        values: &mut Vec<Self>,
        element: pest::iterators::Pair<Rule>,
        indent: usize,
    ) -> Result<(), pest::error::Error<Rule>> {
        Structured::update_indent(values, &element, indent)?;
        values.push(Structured {
            indentation: Indentation::MoreThan(element.as_str().to_owned(), indent),
            children: vec![],
        });
        Ok(())
    }

    fn update_indent_item(
        values: &mut Vec<Self>,
        element: pest::iterators::Pair<Rule>,
        indent: usize,
    ) -> Result<(), pest::error::Error<Rule>> {
        Structured::update_indent(values, &element, indent)?;
        values
            .last_mut()
            .unwrap()
            .children
            .push(Either::Left(element.as_str().to_owned()));
        Ok(())
    }

    fn print(&self, indent: usize) {
        let indent_string = std::iter::repeat(' ').take(indent).collect::<String>();
        let indent = match &self.indentation {
            Indentation::TopLevel => 0,
            Indentation::Exactly(pair, indent) => {
                println!("{}|{}", indent_string, pair);
                *indent
            }
            Indentation::MoreThan(_, _) => panic!("Unexpected more than"),
        };
        let indent_string = std::iter::repeat(' ').take(indent).collect::<String>();
        self.children.iter().for_each(|child| match child {
            Either::Left(pair) => println!("{}|{}", indent_string, pair),
            Either::Right(value) => value.print(indent),
        });
    }
}

impl Template {
    fn parse_comment(comment: pest::iterators::Pair<Rule>) -> () {
        let mut parts = comment.into_inner();
        let indentation = parts.next().unwrap().as_str();
        let comment = parts.next().unwrap();
        let result = WithIndentation::new(indentation, comment);
    }

    fn get_indent(comment: pest::iterators::Pair<Rule>) -> (usize, pest::iterators::Pair<Rule>) {
        let mut parts = comment.into_inner();
        let indentation = compute_indent(&parts.next().unwrap());
        let comment = parts.next().unwrap();
        (indentation, comment)
    }

    pub fn parse(string: &str) -> Result<(), pest::error::Error<Rule>> {
        let mut result = TemplateParser::parse(Rule::rules, string)?;
        let mut values = vec![Structured {
            indentation: Indentation::TopLevel,
            children: vec![],
        }];
        let pair = result.next().unwrap();
        let mut pos = pair.as_span().start_pos();
        pair.into_inner()
            .try_for_each(|pair| match pair.as_rule() {
                Rule::comment | Rule::item => {
                    let (indentation, node) = Template::get_indent(pair);
                    Structured::update_indent_item(&mut values, node, indentation)
                }
                Rule::loop_spec => {
                    let (indentation, node) = Template::get_indent(pair);
                    pos = node.as_span().start_pos();
                    Structured::update_indent_loop_spec(&mut values, node, indentation)
                }
                Rule::EOI => Ok(()),
                _ => panic!("Unexpected rule: {:?}", pair.as_rule()),
            })?;
        Structured::collapse(&mut values, pos)?;
        let structure = values.pop().unwrap();
        structure.print(0);
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_object_access() {
        assert!(ObjectAccess::parse("").is_err());
        assert_eq!(
            ObjectAccess::parse("test"),
            Ok(ObjectAccess(vec![String::from("test")]))
        );
        assert_eq!(
            ObjectAccess::parse("test.hello"),
            Ok(ObjectAccess(vec!["test".to_string(), "hello".to_string()]))
        );
        assert_eq!(
            ObjectAccess::parse("test. hello"),
            Ok(ObjectAccess(vec!["test".to_string(), "hello".to_string()]))
        );
        assert_eq!(
            ObjectAccess::parse("مرحبا"),
            Ok(ObjectAccess(vec!["مرحبا".to_string()]))
        );
        assert_eq!(
            ObjectAccess::parse("مرحبا.بكم"),
            Ok(ObjectAccess(vec![
                "مرحبا".to_string(),
                "بكم".to_string()
            ]))
        );
    }

    #[test]
    fn test_compute_indent_str() {
        assert_eq!(compute_indent_str(""), 0);
        assert_eq!(compute_indent_str(" "), 1);
        assert_eq!(compute_indent_str("\t"), 8);
        assert_eq!(compute_indent_str(" \t"), 8);
        assert_eq!(compute_indent_str("   \t \t"), 16);
        assert_eq!(compute_indent_str("   \t\t"), 16);
        assert_eq!(compute_indent_str("       \t"), 8);
        assert_eq!(compute_indent_str("        \t"), 16);
    }
}

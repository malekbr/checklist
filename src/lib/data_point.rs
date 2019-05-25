use std::collections::{btree_map, BTreeMap};
use std::iter::Peekable;

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

#[derive(PartialEq, Debug)]
pub enum ParseError {
    InvalidObjectAccess(String),
    EmptyObjectAccess,
}

impl ObjectAccess {
    pub fn parse(string: &str) -> Result<Self, ParseError> {
        if string.is_empty() {
            return Err(ParseError::EmptyObjectAccess);
        }
        string.chars().try_for_each(|c| {
            if c.is_whitespace() {
                Err(ParseError::InvalidObjectAccess(String::from(string)))
            } else {
                Ok(())
            }
        })?;
        Ok(ObjectAccess(
            string
                .split('.')
                .map(|string| String::from(string))
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
    Loop(ObjectAccess, Vec<TodoTemplate>),
}

struct Template {
    requires: Fillable,
    templates: Vec<TodoTemplate>,
    fillables: BTreeMap<String, Fillable>,
}
#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_object_access() {
        assert_eq!(ObjectAccess::parse(""), Err(ParseError::EmptyObjectAccess));
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
            Err(ParseError::InvalidObjectAccess("test. hello".to_string()))
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
}

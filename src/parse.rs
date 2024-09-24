use serde::{Deserialize, Serialize};
#[derive(Serialize, Deserialize, Debug)]
#[serde(transparent)]
pub struct Module {
    pub decls: Vec<Decl>,
}

#[derive(Serialize, Deserialize, Debug)]
pub enum Decl {
    ExternMod(String, String),
    Use(String, Vec<String>),
    Func(Visibility, String, Vec<QualifiedName>),
}

#[derive(Serialize, Deserialize, Debug, PartialEq, Eq)]
pub enum Visibility {
    Public,
    Private,
}

#[derive(Serialize, Deserialize, Debug)]
pub struct QualifiedName {
    pub qualifiers: Vec<String>,
    pub base: String,
}

//! The executable records and their views as the spec's records, and the
//! views of lists of them.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// A field line (§5.2), viewed as [`FieldLine`].
#[derive(Debug, PartialEq, Eq)]
pub struct FieldLineBuf {
    /// The field name.
    pub name: Vec<u8>,
    /// The field line value (without leading and trailing whitespace).
    pub value: Vec<u8>,
}

impl View for FieldLineBuf {
    type V = FieldLine;

    open spec fn view(&self) -> FieldLine {
        FieldLine { name: self.name@, value: self.value@ }
    }
}

/// A parameter (§5.6.6), viewed as [`Parameter`].
#[derive(Debug, PartialEq, Eq)]
pub struct ParameterBuf {
    /// The parameter name, as received.
    pub name: Vec<u8>,
    /// The parameter value, unquoted.
    pub value: Vec<u8>,
}

impl View for ParameterBuf {
    type V = Parameter;

    open spec fn view(&self) -> Parameter {
        Parameter { name: self.name@, value: self.value@ }
    }
}

/// A transfer coding (§10.1.4), viewed as [`TransferCoding`].
#[derive(Debug, PartialEq, Eq)]
pub struct TransferCodingBuf {
    /// The coding's name, as received.
    pub name: Vec<u8>,
    /// Its parameters.
    pub parameters: Vec<ParameterBuf>,
}

impl View for TransferCodingBuf {
    type V = TransferCoding;

    open spec fn view(&self) -> TransferCoding {
        TransferCoding { name: self.name@, parameters: params_view(self.parameters@) }
    }
}

/// The view of a list of strings.
pub open spec fn strings_view(v: Seq<Vec<u8>>) -> Seq<Seq<u8>> {
    v.map_values(|e: Vec<u8>| e@)
}

/// The view of a list of field lines.
pub open spec fn lines_view(v: Seq<FieldLineBuf>) -> Seq<FieldLine> {
    v.map_values(|e: FieldLineBuf| e@)
}

/// The view of a list of parameters.
pub open spec fn params_view(v: Seq<ParameterBuf>) -> Seq<Parameter> {
    v.map_values(|e: ParameterBuf| e@)
}

/// The view of a list of transfer codings.
pub open spec fn codings_view(v: Seq<TransferCodingBuf>) -> Seq<TransferCoding> {
    v.map_values(|e: TransferCodingBuf| e@)
}

} // verus!

pub const AND_OPERATOR_SYMBOL:char='+';
/*
 * WARNING
 *  
 * Always make these symbols different from each other.
 * Same symbols with different meanings might end up
 * in inconsistent behaviour by the parser
 */
pub const OR_OPERATOR_SYMBOL:char='*';
pub const XOR_OPERATOR_SYMBOL:char='%';
pub const IFF_OPERATOR_SYMBOL:char='=';
pub const IMPL_OPERATOR_SYMBOL:char='>';
pub const LEFT_IMPL_OPERATOR_SYMBOL:char='<';
pub const TRUE_ATOM_SYMBOL:char='T';
pub const FALSE_ATOM_SYMBOL:char='F';
pub const FRESH_VARIABLE_SYMBOL:char='f';
pub const EXISTENTIAL_QUANTIFIER_SYMBOL:char='E';
pub const UNIVERSAL_QUANTIFIER_SYMBOL:char='A';
pub const NEGATION_OPERATOR_SYMBOL:char='-';
pub const QUANTIFIER_SEPARATOR_SYMBOL:char='.';
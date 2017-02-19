use std::cell::{Cell, RefCell};
use std::result;

use ast::{self, Ast, Span};
use either::Either;
use hir::{self, Error, ErrorKind, Hir};
use unicode::{self, ClassQuery};

type Result<T> = result::Result<T, Error>;

/// A builder for constructing an AST->HIR translator.
#[derive(Clone, Debug)]
pub struct TranslatorBuilder {
    allow_invalid_utf8: bool,
}

impl Default for TranslatorBuilder {
    fn default() -> TranslatorBuilder {
        TranslatorBuilder::new()
    }
}

impl TranslatorBuilder {
    /// Create a new translator builder with a default c onfiguration.
    pub fn new() -> TranslatorBuilder {
        TranslatorBuilder {
            allow_invalid_utf8: false,
        }
    }

    /// Build a translator using the current configuration.
    pub fn build<'a>(&self) -> Translator<'a> {
        Translator {
            stack: RefCell::new(vec![]),
            stack_class_bytes: RefCell::new(vec![]),
            stack_class_unicode: RefCell::new(vec![]),
            flags: Cell::new(Flags::default()),
            next_capture_index: Cell::new(1),
            allow_invalid_utf8: self.allow_invalid_utf8,
        }
    }

    /// When enabled, translation will permit the construction of a regular
    /// expression that may match invalid UTF-8.
    ///
    /// When disabled (the default), the translator is guaranteed to produce
    /// an expression that will only ever match valid UTF-8 (otherwise, the
    /// translator will return an error).
    pub fn allow_invalid_utf8(
        &mut self,
        yes: bool,
    ) -> &mut TranslatorBuilder {
        self.allow_invalid_utf8 = yes;
        self
    }
}

/// A translator maps abstract syntax to a high level intermediate
/// representation.
///
/// A translator may be benefit from reuse. That is, a translator can translate
/// many abstract syntax trees.
///
/// The lifetime `'a` refers to the lifetime of the abstract syntax tree that
/// is being translated.
#[derive(Clone, Debug)]
pub struct Translator<'a> {
    /// A stack of recursive cases over Ast.
    stack: RefCell<Vec<Induct<'a>>>,
    /// A stack of recursive cases over ast::Class, for bytes.
    stack_class_bytes: RefCell<Vec<ClassInduct<'a, hir::ClassBytes>>>,
    /// A stack of recursive cases over ast::Class, for Unicode.
    stack_class_unicode: RefCell<Vec<ClassInduct<'a, hir::ClassUnicode>>>,
    /// The current flag settings.
    flags: Cell<Flags>,
    /// The next capture index.
    next_capture_index: Cell<u32>,
    /// Whether we're allowed to produce HIR that can match arbitrary bytes.
    allow_invalid_utf8: bool,
}

/// Represents either a recursive case analysis over an Ast, or a base case
/// that yields an HIR expression.
#[derive(Clone, Debug)]
enum Case<'a> {
    Base(Hir),
    Induct(Induct<'a>),
}

/// A recursive case analysis over an Ast.
///
/// More practically, one can think of this as the stack frame at the time
/// of a recursive call. Note that some cases (for concatenation and
/// alternation) make multiple recursive calls in sequence, which is reflected
/// in the state of the stack frame.
#[derive(Clone, Debug)]
enum Induct<'a> {
    /// This represents the stack frame after making a recursive call on
    /// a group's subexpression. The flags of the group are set on the
    /// Translator, and the previous flags are recorded here in this stack
    /// frame.
    Group {
        group: &'a ast::Group,
        flags: Option<Flags>,
    },
    /// This represents the stack frame after making a recursive call on a
    /// repetition operation's subexpression.
    Repetition(&'a ast::Repetition),
    /// This represents the stack frame during *all* of the recursive calls
    /// to each subexpression in a concatenation. `head` represents the current
    /// subexpression being translated while `tail` represents the remaining
    /// subexpressions. `exprs` represents the translation of previous
    /// subexpressions to HIR expressions.
    Concat {
        exprs: Vec<Hir>,
        head: &'a Ast,
        tail: &'a [Ast],
    },
    /// This represents the stack frame during *all* of the recursive calls
    /// to each subexpression in an alternation. `head` represents the current
    /// subexpression being translated while `tail` represents the remaining
    /// subexpressions. `exprs` represents the translation of previous
    /// subexpressions to HIR expressions.
    Alternation {
        exprs: Vec<Hir>,
        head: &'a Ast,
        tail: &'a [Ast],
    },
}

impl<'a> Translator<'a> {
    /// Create a new translator using the default configuration.
    pub fn new() -> Translator<'a> {
        TranslatorBuilder::new().build()
    }

    /// Translate the given abstract syntax tree (AST) into a high level
    /// intermediate representation (HIR).
    ///
    /// If there was a problem doing the translation, then an HIR-specific
    /// error is returned.
    pub fn translate(&self, mut ast: &'a Ast) -> Result<Hir> {
        // Ensure that we start with a clean slate.
        self.stack.borrow_mut().clear();
        self.stack_class_bytes.borrow_mut().clear();
        self.stack_class_unicode.borrow_mut().clear();
        self.flags.set(Flags::default());
        self.next_capture_index.set(1);

    'LOOP:
        loop {
            // Structural induction. If the AST has a sub-expression, then
            // push it on to the stack and descend.
            let mut base = match try!(self.induct(ast)) {
                Case::Base(base) => base,
                Case::Induct(x) => {
                    ast = x.next_child_ast();
                    self.stack.borrow_mut().push(x);
                    continue 'LOOP;
                }
            };
            // Otherwise, if we have a base case, pop our stack until we either
            // need to make another recursive call or we've finished.
            loop {
                let frame = match self.stack.borrow_mut().pop() {
                    None => return Ok(base),
                    Some(frame) => frame,
                };
                base = match self.pop(frame, base) {
                    Case::Base(base) => base,
                    Case::Induct(x) => {
                        ast = x.next_child_ast();
                        self.stack.borrow_mut().push(x);
                        continue 'LOOP;
                    }
                }
            }
        }
    }

    /// Induct performs case analysis on any regex abstract syntax tree, and
    /// either returns an HIR expression or a continuation that represents
    /// structural induction on the AST. In other words, this is a
    /// representation of recursion.
    fn induct(&self, ast: &'a Ast) -> Result<Case<'a>> {
        Ok(match *ast {
            Ast::Empty(_) => Case::Base(Hir::Empty),
            Ast::Flags(ref x) => {
                self.set_flags(&x.flags);
                Case::Base(Hir::Empty)
            }
            Ast::Literal(ref x) => Case::Base(try!(self.hir_literal(x))),
            Ast::Dot(span) => Case::Base(try!(self.hir_dot(span))),
            Ast::Assertion(ref x) => Case::Base(self.hir_assertion(x)),
            Ast::Class(ref x) => {
                if self.flags.get().unicode() {
                    let trans = ClassUnicodeTranslator::new(self);
                    let cls = try!(trans.translate(x));
                    Case::Base(Hir::Class(hir::Class::Unicode(cls)))
                } else {
                    let trans = ClassBytesTranslator::new(self);
                    let cls = try!(trans.translate(x));
                    Case::Base(Hir::Class(hir::Class::Bytes(cls)))
                }
            }
            Ast::Repetition(ref x) => Case::Induct(Induct::Repetition(x)),
            Ast::Group(ref x) => {
                let flags = match x.flags() {
                    None => None,
                    Some(ast_flags) => Some(self.set_flags(ast_flags)),
                };
                Case::Induct(Induct::Group {
                    group: x,
                    flags: flags,
                })
            }
            Ast::Concat(ref x) if x.asts.is_empty() => {
                Case::Base(Hir::Empty)
            }
            Ast::Concat(ref x) => {
                Case::Induct(Induct::Concat {
                    exprs: vec![],
                    head: &x.asts[0],
                    tail: &x.asts[1..],
                })
            }
            Ast::Alternation(ref x) if x.asts.is_empty() => {
                Case::Base(Hir::Empty)
            }
            Ast::Alternation(ref x) => {
                Case::Induct(Induct::Alternation {
                    exprs: vec![],
                    head: &x.asts[0],
                    tail: &x.asts[1..],
                })
            }
        })
    }

    /// Pop a recursive call. This either returns an expression or a
    /// continuation to another recursive call.
    fn pop(&self, case: Induct<'a>, expr: Hir) -> Case<'a> {
        match case {
            Induct::Group { group, flags } => {
                if let Some(flags) = flags {
                    self.flags.set(flags);
                }
                Case::Base(self.hir_group(group, expr))
            }
            Induct::Repetition(rep) => {
                Case::Base(self.hir_repetition(rep, expr))
            }
            Induct::Concat { mut exprs, tail, .. } => {
                if !expr.is_empty() {
                    exprs.push(expr);
                }
                if tail.is_empty() {
                    if exprs.is_empty() {
                        Case::Base(Hir::Empty)
                    } else {
                        Case::Base(Hir::Concat(exprs))
                    }
                } else {
                    Case::Induct(Induct::Concat {
                        exprs: exprs,
                        head: &tail[0],
                        tail: &tail[1..],
                    })
                }
            }
            Induct::Alternation { mut exprs, tail, .. } => {
                exprs.push(expr);
                if tail.is_empty() {
                    Case::Base(Hir::Alternation(exprs))
                } else {
                    Case::Induct(Induct::Alternation {
                        exprs: exprs,
                        head: &tail[0],
                        tail: &tail[1..],
                    })
                }
            }
        }
    }

    /// Set the flags of this translator from the flags set in the given AST.
    /// Then, return the old flags.
    fn set_flags(&self, ast_flags: &ast::Flags) -> Flags {
        let old_flags = self.flags.get();
        let mut new_flags = Flags::from_ast(ast_flags);
        new_flags.merge(&old_flags);
        self.flags.set(new_flags);
        old_flags
    }

    /// Increment the current capture index and return the old one.
    fn next_capture_index(&self) -> u32 {
        let i = self.next_capture_index.get();
        self.next_capture_index.set(i + 1);
        i
    }

    // The following methods are all constructor functions for converting
    // ASTs to HIR expressions. That is, these are our base cases.

    fn hir_literal(&self, lit: &ast::Literal) -> Result<Hir> {
        let ch = match try!(self.literal_to_char(lit)) {
            Either::Right(byte) => return Ok(Hir::Literal(byte)),
            Either::Left(ch) => ch,
        };
        if self.flags.get().case_insensitive() {
            self.hir_from_char_case_insensitive(lit.span, ch)
        } else {
            self.hir_from_char(lit.span, ch)
        }
    }

    fn literal_to_char(&self, lit: &ast::Literal) -> Result<Either<char, u8>> {
        if self.flags.get().unicode() {
            return Ok(Either::Left(lit.c));
        }
        let byte = match lit.byte() {
            None => return Ok(Either::Left(lit.c)),
            Some(byte) => byte,
        };
        if byte > 0x7F && !self.allow_invalid_utf8 {
            return Err(Error {
                span: lit.span,
                kind: ErrorKind::InvalidUtf8,
            });
        }
        Ok(Either::Right(byte))
    }

    fn hir_from_char(&self, span: Span, c: char) -> Result<Hir> {
        if !self.flags.get().unicode() && c.len_utf8() > 1 {
            return Err(Error {
                span: span,
                kind: ErrorKind::UnicodeNotAllowed,
            });
        }

        let mut buf = [0u8; 4];
        let bytes = c.encode_utf8(&mut buf).as_bytes();
        assert!(!bytes.is_empty());

        Ok(if bytes.len() == 1 {
            Hir::Literal(bytes[0])
        } else {
            Hir::Concat(bytes.iter().cloned().map(Hir::Literal).collect())
        })
    }

    fn hir_from_char_case_insensitive(
        &self,
        span: Span,
        c: char,
    ) -> Result<Hir> {
        if !self.flags.get().unicode() && c.len_utf8() > 1 {
            return Err(Error {
                span: span,
                kind: ErrorKind::UnicodeNotAllowed,
            });
        }

        let mut cls = hir::ClassUnicode::new(vec![
            hir::ClassRangeUnicode::new(c, c),
        ]);
        cls.case_fold_simple();
        Ok(Hir::Class(hir::Class::Unicode(cls)))
    }

    fn hir_dot(&self, span: Span) -> Result<Hir> {
        let unicode = self.flags.get().unicode();
        Ok(if self.flags.get().dot_matches_new_line() {
            Hir::Class(if unicode {
                let ranges = vec![
                    hir::ClassRangeUnicode::new('\0', '\u{10FFFF}'),
                ];
                hir::Class::Unicode(hir::ClassUnicode::new(ranges))
            } else {
                if !self.allow_invalid_utf8 {
                    return Err(Error {
                        span: span,
                        kind: ErrorKind::InvalidUtf8,
                    });
                }
                let ranges = vec![
                    hir::ClassRangeBytes::new(b'\0', b'\xFF'),
                ];
                hir::Class::Bytes(hir::ClassBytes::new(ranges))
            })
        } else {
            Hir::Class(if unicode {
                let ranges = vec![
                    hir::ClassRangeUnicode::new('\0', '\x09'),
                    hir::ClassRangeUnicode::new('\x0B', '\u{10FFFF}'),
                ];
                hir::Class::Unicode(hir::ClassUnicode::new(ranges))
            } else {
                if !self.allow_invalid_utf8 {
                    return Err(Error {
                        span: span,
                        kind: ErrorKind::InvalidUtf8,
                    });
                }
                let ranges = vec![
                    hir::ClassRangeBytes::new(b'\0', b'\x09'),
                    hir::ClassRangeBytes::new(b'\x0B', b'\xFF'),
                ];
                hir::Class::Bytes(hir::ClassBytes::new(ranges))
            })
        })
    }

    fn hir_assertion(&self, asst: &ast::Assertion) -> Hir {
        let unicode = self.flags.get().unicode();
        let multi_line = self.flags.get().multi_line();
        match asst.kind {
            ast::AssertionKind::StartLine => {
                Hir::Anchor(if multi_line {
                    hir::Anchor::StartLine
                } else {
                    hir::Anchor::StartText
                })
            }
            ast::AssertionKind::EndLine => {
                Hir::Anchor(if multi_line {
                    hir::Anchor::EndLine
                } else {
                    hir::Anchor::EndText
                })
            }
            ast::AssertionKind::StartText => {
                Hir::Anchor(hir::Anchor::StartText)
            }
            ast::AssertionKind::EndText => {
                Hir::Anchor(hir::Anchor::EndText)
            }
            ast::AssertionKind::WordBoundary => {
                Hir::WordBoundary(if unicode {
                    hir::WordBoundary::Unicode
                } else {
                    hir::WordBoundary::Ascii
                })
            }
            ast::AssertionKind::NotWordBoundary => {
                Hir::WordBoundary(if unicode {
                    hir::WordBoundary::UnicodeNegate
                } else {
                    hir::WordBoundary::AsciiNegate
                })
            }
        }
    }

    fn hir_group(&self, group: &ast::Group, expr: Hir) -> Hir {
        let kind = match group.kind {
            ast::GroupKind::CaptureIndex => {
                hir::GroupKind::CaptureIndex(self.next_capture_index())
            }
            ast::GroupKind::CaptureName(ref capname) => {
                hir::GroupKind::CaptureName {
                    name: capname.name.clone(),
                    index: self.next_capture_index(),
                }
            }
            ast::GroupKind::NonCapturing(_) => hir::GroupKind::NonCapturing,
        };
        Hir::Group(hir::Group {
            kind: kind,
            hir: Box::new(expr),
        })
    }

    fn hir_repetition(&self, rep: &ast::Repetition, expr: Hir) -> Hir {
        let kind = match rep.op.kind {
            ast::RepetitionKind::ZeroOrOne => hir::RepetitionKind::ZeroOrOne,
            ast::RepetitionKind::ZeroOrMore => hir::RepetitionKind::ZeroOrMore,
            ast::RepetitionKind::OneOrMore => hir::RepetitionKind::OneOrMore,
            ast::RepetitionKind::Range(ast::RepetitionRange::Exactly(m)) => {
                hir::RepetitionKind::Range(hir::RepetitionRange::Exactly(m))
            }
            ast::RepetitionKind::Range(ast::RepetitionRange::AtLeast(m)) => {
                hir::RepetitionKind::Range(hir::RepetitionRange::AtLeast(m))
            }
            ast::RepetitionKind::Range(ast::RepetitionRange::Bounded(m,n)) => {
                hir::RepetitionKind::Range(hir::RepetitionRange::Bounded(m, n))
            }
        };
        let greedy =
            if self.flags.get().swap_greed() {
                !rep.greedy
            } else {
                rep.greedy
            };
        Hir::Repetition(hir::Repetition {
            kind: kind,
            greedy: greedy,
            hir: Box::new(expr),
        })
    }
}

impl<'a> Induct<'a> {
    /// Return the next AST to perform case analysis on.
    ///
    /// This corresponds to the next sub-expression to process in the current
    /// stack frame.
    fn next_child_ast(&self) -> &'a Ast {
        match *self {
            Induct::Group { ref group, .. } => &group.ast,
            Induct::Repetition(rep) => &rep.ast,
            Induct::Concat { head, .. } => head,
            Induct::Alternation { head, .. } => head,
        }
    }
}

#[derive(Clone, Debug)]
enum ClassCase<C, I> {
    Base(C),
    Induct(I),
}

type ClassUnicodeCase<'a> = ClassCase<
    hir::ClassUnicode,
    ClassInduct<'a, hir::ClassUnicode>,
>;

type ClassBytesCase<'a> = ClassCase<
    hir::ClassBytes,
    ClassInduct<'a, hir::ClassBytes>,
>;

#[derive(Clone, Debug)]
enum ClassInduct<'a, C> {
    Union {
        class: C,
        negated: bool,
        head: &'a ast::Class,
        tail: &'a [ast::ClassSetItem],
    },
    BinaryLHS {
        op: &'a ast::ClassSetBinaryOpKind,
        negated: bool,
        lhs: &'a ast::ClassSetOp,
        rhs: &'a ast::ClassSetOp,
    },
    BinaryRHS {
        op: &'a ast::ClassSetBinaryOpKind,
        negated: bool,
        lhs: C,
        rhs: &'a ast::ClassSetOp,
    },
}

impl<'a, C> ClassInduct<'a, C> {
    /// Return the next AST to induct over.
    ///
    /// This returns either an arbitrary ast::Class or a specific
    /// ast::ClassSetOp. The latter supports cases like `[a-c&&b-d]` where the
    /// `&&` binary operator represents its operands as `a-c` and `b-d` instead
    /// of as proper nested classes like `[a-c]` and `[b-d]`.
    fn next_child_ast(&self) -> Either<&'a ast::Class, &'a ast::ClassSetOp> {
        match *self {
            ClassInduct::Union { head, .. } => Either::Left(head),
            ClassInduct::BinaryLHS { ref lhs, .. } => Either::Right(lhs),
            ClassInduct::BinaryRHS { ref rhs, .. } => Either::Right(rhs),
        }
    }
}

/// A translator just for Unicode character classes.
///
/// The lifetime `'a` corresponds to the lifetime of the AST we're translating.
/// The lifetime `'t` corresponds to the lifetime of the top-level AST
/// translator.
#[derive(Clone, Debug)]
struct ClassUnicodeTranslator<'a: 't, 't> {
    trans: &'t Translator<'a>,
}

impl<'a, 't> ClassUnicodeTranslator<'a, 't> {
    fn new(trans: &'t Translator<'a>) -> ClassUnicodeTranslator<'a, 't> {
        ClassUnicodeTranslator { trans: trans }
    }

    fn stack(&self) -> &RefCell<Vec<ClassInduct<'a, hir::ClassUnicode>>> {
        &self.trans.stack_class_unicode
    }

    fn translate(&self, ast: &'a ast::Class) -> Result<hir::ClassUnicode> {
        // The only way to get a Unicode class is by enabling Unicode mode.
        assert!(self.trans.flags.get().unicode());

        let mut ast = Either::Left(ast);
    'LOOP:
        loop {
            let mut base = match try!(self.induct(ast)) {
                ClassCase::Base(base) => base,
                ClassCase::Induct(x) => {
                    ast = x.next_child_ast();
                    self.stack().borrow_mut().push(x);
                    continue 'LOOP;
                }
            };
            loop {
                let frame = match self.stack().borrow_mut().pop() {
                    None => return Ok(base),
                    Some(frame) => frame,
                };
                base = match try!(self.pop(frame, base)) {
                    ClassCase::Base(base) => base,
                    ClassCase::Induct(x) => {
                        ast = x.next_child_ast();
                        self.stack().borrow_mut().push(x);
                        continue 'LOOP;
                    }
                }
            }
        }
    }

    fn induct(
        &self,
        ast: Either<&'a ast::Class, &'a ast::ClassSetOp>,
    ) -> Result<ClassUnicodeCase<'a>> {
        Ok(match ast {
            Either::Left(&ast::Class::Unicode(ref x)) => {
                ClassCase::Base(try!(self.hir_unicode_class(x)))
            }
            Either::Left(&ast::Class::Perl(ref x)) => {
                ClassCase::Base(self.hir_perl_class(x))
            }
            Either::Left(&ast::Class::Set(ref cls)) => {
                try!(self.case_from_class_set_op(&cls.op, cls.negated))
            }
            Either::Right(op) => {
                try!(self.case_from_class_set_op(op, false))
            }
        })
    }

    fn pop(
        &self,
        case: ClassInduct<'a, hir::ClassUnicode>,
        expr: hir::ClassUnicode,
    ) -> Result<ClassUnicodeCase<'a>> {
        use self::ClassInduct::*;
        Ok(match case {
            Union { mut class, negated, tail, .. } => {
                class.union(&expr);
                let rest = try!(self.union_into_class(tail, &mut class));
                if let Some((ast_class, tail)) = rest {
                    ClassCase::Induct(ClassInduct::Union {
                        class: class,
                        negated: negated,
                        head: ast_class,
                        tail: tail,
                    })
                } else {
                    ClassCase::Base(self.fold_and_negate(class, negated))
                }
            }
            BinaryLHS { op, negated, rhs, .. } => {
                ClassCase::Induct(ClassInduct::BinaryRHS {
                    op: op,
                    negated: negated,
                    lhs: expr,
                    rhs: rhs,
                })
            }
            BinaryRHS { op, negated, mut lhs, .. } => {
                use ast::ClassSetBinaryOpKind::*;
                match *op {
                    Intersection => lhs.intersect(&expr),
                    Difference => lhs.difference(&expr),
                    SymmetricDifference => lhs.symmetric_difference(&expr),
                }
                ClassCase::Base(self.fold_and_negate(lhs, negated))
            }
        })
    }

    fn case_from_class_set_op(
        &self,
        ast: &'a ast::ClassSetOp,
        negated: bool,
    ) -> Result<ClassUnicodeCase<'a>> {
        Ok(match *ast {
            ast::ClassSetOp::Union(ref union) => {
                let mut cls = hir::ClassUnicode::empty();
                let rest = try!(self.union_into_class(&union.items, &mut cls));
                if let Some((ast_class, tail)) = rest {
                    ClassCase::Induct(ClassInduct::Union {
                        class: cls,
                        negated: negated,
                        head: ast_class,
                        tail: tail,
                    })
                } else {
                    ClassCase::Base(self.fold_and_negate(cls, negated))
                }
            }
            ast::ClassSetOp::BinaryOp(ref op) => {
                ClassCase::Induct(ClassInduct::BinaryLHS {
                    op: &op.kind,
                    negated: negated,
                    lhs: &op.lhs,
                    rhs: &op.rhs,
                })
            }
        })
    }

    fn union_into_class(
        &self,
        items: &'a [ast::ClassSetItem],
        cls: &mut hir::ClassUnicode,
    ) -> Result<Option<(&'a ast::Class, &'a [ast::ClassSetItem])>> {
        use ast::ClassSetItem::*;
        for i in 0..items.len() {
            match items[i] {
                Literal(ref x) => {
                    cls.push(hir::ClassRangeUnicode::new(x.c, x.c));
                }
                Range(ref x) => {
                    cls.push(hir::ClassRangeUnicode::new(x.start.c, x.end.c));
                }
                Ascii(ref x) => {
                    for &(s, e) in ascii_class(&x.kind) {
                        cls.push(hir::ClassRangeUnicode::new(s, e));
                    }
                }
                Class(ref ast_class) => {
                    return Ok(Some((ast_class, &items[i+1..])));
                }
            }
        }
        Ok(None)
    }

    fn hir_unicode_class(
        &self,
        ast_class: &ast::ClassUnicode,
    ) -> Result<hir::ClassUnicode> {
        use ast::ClassUnicodeKind::*;

        let query = match ast_class.kind {
            OneLetter(name) => ClassQuery::OneLetter(name),
            Named(ref name) => ClassQuery::Binary(name),
            NamedValue { ref name, ref value, .. } => {
                ClassQuery::ByValue {
                    property_name: name,
                    property_value: value,
                }
            }
        };
        let mut class = match unicode::class(query) {
            Ok(class) => class,
            Err(unicode::Error::PropertyNotFound) => {
                return Err(Error {
                    span: ast_class.span,
                    kind: ErrorKind::UnicodePropertyNotFound,
                });
            }
            Err(unicode::Error::PropertyValueNotFound) => {
                return Err(Error {
                    span: ast_class.span,
                    kind: ErrorKind::UnicodePropertyValueNotFound,
                });
            }
        };
        // Note that we must apply case folding before negation!
        // Consider `(?i)[^x]`. If we applied negation field, then
        // the result would be the character class that matched any
        // Unicode scalar value.
        if self.trans.flags.get().case_insensitive() {
            class.case_fold_simple();
        }
        if ast_class.negated {
            class.negate();
        }
        Ok(class)
    }

    fn hir_perl_class(&self, ast_class: &ast::ClassPerl) -> hir::ClassUnicode {
        use ast::ClassPerlKind::*;
        use unicode_tables::perl_word::PERL_WORD;

        let mut class = match ast_class.kind {
            Digit => {
                let query = ClassQuery::Binary("Decimal_Number");
                unicode::class(query).unwrap()
            }
            Space => {
                let query = ClassQuery::Binary("Whitespace");
                unicode::class(query).unwrap()
            }
            Word => unicode::hir_class(PERL_WORD),
        };
        // We needn't apply case folding here because the Perl Unicode classes
        // are already closed under Unicode simple case folding.
        if ast_class.negated {
            class.negate();
        }
        class
    }

    fn fold_and_negate(
        &self,
        mut class: hir::ClassUnicode,
        negated: bool,
    ) -> hir::ClassUnicode {
        if self.trans.flags.get().case_insensitive() {
            class.case_fold_simple();
        }
        if negated {
            class.negate();
        }
        class
    }
}

/// A translator just for byte character classes.
///
/// The lifetime `'a` corresponds to the lifetime of the AST we're translating.
/// The lifetime `'t` corresponds to the lifetime of the top-level AST
/// translator.
#[derive(Clone, Debug)]
struct ClassBytesTranslator<'a: 't, 't> {
    trans: &'t Translator<'a>,
}

impl<'a, 't> ClassBytesTranslator<'a, 't> {
    fn new(trans: &'t Translator<'a>) -> ClassBytesTranslator<'a, 't> {
        ClassBytesTranslator { trans: trans }
    }

    fn stack(&self) -> &RefCell<Vec<ClassInduct<'a, hir::ClassBytes>>> {
        &self.trans.stack_class_bytes
    }

    fn translate(&self, ast: &'a ast::Class) -> Result<hir::ClassBytes> {
        // The only way to get a byte class is by disabling Unicode mode.
        assert!(!self.trans.flags.get().unicode());

        let mut ast = Either::Left(ast);
    'LOOP:
        loop {
            let mut base = match try!(self.induct(ast)) {
                ClassCase::Base(base) => base,
                ClassCase::Induct(x) => {
                    ast = x.next_child_ast();
                    self.stack().borrow_mut().push(x);
                    continue 'LOOP;
                }
            };
            loop {
                let frame = match self.stack().borrow_mut().pop() {
                    None => return Ok(base),
                    Some(frame) => frame,
                };
                base = match try!(self.pop(frame, base)) {
                    ClassCase::Base(base) => base,
                    ClassCase::Induct(x) => {
                        ast = x.next_child_ast();
                        self.stack().borrow_mut().push(x);
                        continue 'LOOP;
                    }
                }
            }
        }
    }

    fn induct(
        &self,
        ast: Either<&'a ast::Class, &'a ast::ClassSetOp>,
    ) -> Result<ClassBytesCase<'a>> {
        Ok(match ast {
            Either::Left(&ast::Class::Unicode(ref x)) => {
                return Err(Error {
                    span: x.span,
                    kind: ErrorKind::UnicodeNotAllowed,
                })
            }
            Either::Left(&ast::Class::Perl(ref x)) => {
                ClassCase::Base(self.hir_perl_class(x))
            }
            Either::Left(&ast::Class::Set(ref cls)) => {
                try!(self.case_from_class_set_op(&cls.op, cls.negated))
            }
            Either::Right(op) => {
                try!(self.case_from_class_set_op(op, false))
            }
        })
    }

    fn pop(
        &self,
        case: ClassInduct<'a, hir::ClassBytes>,
        expr: hir::ClassBytes,
    ) -> Result<ClassBytesCase<'a>> {
        use self::ClassInduct::*;
        Ok(match case {
            Union { mut class, negated, tail, .. } => {
                class.union(&expr);
                let rest = try!(self.union_into_class(tail, &mut class));
                if let Some((ast_class, tail)) = rest {
                    ClassCase::Induct(ClassInduct::Union {
                        class: class,
                        negated: negated,
                        head: ast_class,
                        tail: tail,
                    })
                } else {
                    ClassCase::Base(self.fold_and_negate(class, negated))
                }
            }
            BinaryLHS { op, negated, rhs, .. } => {
                ClassCase::Induct(ClassInduct::BinaryRHS {
                    op: op,
                    negated: negated,
                    lhs: expr,
                    rhs: rhs,
                })
            }
            BinaryRHS { op, negated, mut lhs, .. } => {
                use ast::ClassSetBinaryOpKind::*;
                match *op {
                    Intersection => lhs.intersect(&expr),
                    Difference => lhs.difference(&expr),
                    SymmetricDifference => lhs.symmetric_difference(&expr),
                }
                ClassCase::Base(self.fold_and_negate(lhs, negated))
            }
        })
    }

    fn case_from_class_set_op(
        &self,
        ast: &'a ast::ClassSetOp,
        negated: bool,
    ) -> Result<ClassBytesCase<'a>> {
        Ok(match *ast {
            ast::ClassSetOp::Union(ref union) => {
                let mut cls = hir::ClassBytes::empty();
                let rest = try!(self.union_into_class(&union.items, &mut cls));
                if let Some((ast_class, tail)) = rest {
                    ClassCase::Induct(ClassInduct::Union {
                        class: cls,
                        negated: negated,
                        head: ast_class,
                        tail: tail,
                    })
                } else {
                    ClassCase::Base(self.fold_and_negate(cls, negated))
                }
            }
            ast::ClassSetOp::BinaryOp(ref op) => {
                ClassCase::Induct(ClassInduct::BinaryLHS {
                    op: &op.kind,
                    negated: negated,
                    lhs: &op.lhs,
                    rhs: &op.rhs,
                })
            }
        })
    }

    fn union_into_class(
        &self,
        items: &'a [ast::ClassSetItem],
        cls: &mut hir::ClassBytes,
    ) -> Result<Option<(&'a ast::Class, &'a [ast::ClassSetItem])>> {
        use ast::ClassSetItem::*;
        for i in 0..items.len() {
            match items[i] {
                Literal(ref x) => {
                    let byte = try!(self.literal_byte(x));
                    cls.push(hir::ClassRangeBytes::new(byte, byte));
                }
                Range(ref x) => {
                    let start = try!(self.literal_byte(&x.start));
                    let end = try!(self.literal_byte(&x.end));
                    cls.push(hir::ClassRangeBytes::new(start, end));
                }
                Ascii(ref x) => {
                    for &(s, e) in ascii_class(&x.kind) {
                        cls.push(hir::ClassRangeBytes::new(s as u8, e as u8));
                    }
                }
                Class(ref ast_class) => {
                    return Ok(Some((ast_class, &items[i+1..])));
                }
            }
        }
        Ok(None)
    }

    fn hir_perl_class(&self, ast_class: &ast::ClassPerl) -> hir::ClassBytes {
        use ast::ClassPerlKind::*;
        let mut class = match ast_class.kind {
            Digit => hir_ascii_class_bytes(&ast::ClassAsciiKind::Digit),
            Space => hir_ascii_class_bytes(&ast::ClassAsciiKind::Space),
            Word => hir_ascii_class_bytes(&ast::ClassAsciiKind::Word),
        };
        // We needn't apply case folding here because the Perl ASCII classes
        // are already closed (under ASCII case folding).
        if ast_class.negated {
            class.negate();
        }
        class
    }

    fn fold_and_negate(
        &self,
        mut class: hir::ClassBytes,
        negated: bool,
    ) -> hir::ClassBytes {
        if self.trans.flags.get().case_insensitive() {
            class.case_fold_simple();
        }
        if negated {
            class.negate();
        }
        class
    }

    fn literal_byte(&self, ast: &ast::Literal) -> Result<u8> {
        match try!(self.trans.literal_to_char(ast)) {
            Either::Left(ch) => {
                if ch <= 0x7F as char {
                    Ok(ch as u8)
                } else {
                    // We can't feasibly support Unicode in
                    // byte oriented classes. Byte classes don't
                    // do Unicode case folding.
                    Err(Error {
                        span: ast.span,
                        kind: ErrorKind::UnicodeNotAllowed,
                    })
                }
            }
            Either::Right(byte) => Ok(byte),
        }
    }
}

#[derive(Clone, Copy, Debug, Default)]
struct Flags {
    case_insensitive: Option<bool>,
    multi_line: Option<bool>,
    dot_matches_new_line: Option<bool>,
    swap_greed: Option<bool>,
    unicode: Option<bool>,
    // Note that `ignore_whitespace` is omitted here because it is handled
    // entirely in the parser.
}

impl Flags {
    fn from_ast(ast: &ast::Flags) -> Flags {
        let mut flags = Flags::default();
        let mut enable = true;
        for item in &ast.items {
            match item.kind {
                ast::FlagsItemKind::Negation => {
                    enable = false;
                }
                ast::FlagsItemKind::Flag(ast::Flag::CaseInsensitive) => {
                    flags.case_insensitive = Some(enable);
                }
                ast::FlagsItemKind::Flag(ast::Flag::MultiLine) => {
                    flags.multi_line = Some(enable);
                }
                ast::FlagsItemKind::Flag(ast::Flag::DotMatchesNewLine) => {
                    flags.dot_matches_new_line = Some(enable);
                }
                ast::FlagsItemKind::Flag(ast::Flag::SwapGreed) => {
                    flags.swap_greed = Some(enable);
                }
                ast::FlagsItemKind::Flag(ast::Flag::Unicode) => {
                    flags.unicode = Some(enable);
                }
                ast::FlagsItemKind::Flag(ast::Flag::IgnoreWhitespace) => {}
            }
        }
        flags
    }

    fn merge(&mut self, previous: &Flags) {
        if self.case_insensitive.is_none() {
            self.case_insensitive = previous.case_insensitive;
        }
        if self.multi_line.is_none() {
            self.multi_line = previous.multi_line;
        }
        if self.dot_matches_new_line.is_none() {
            self.dot_matches_new_line = previous.dot_matches_new_line;
        }
        if self.swap_greed.is_none() {
            self.swap_greed = previous.swap_greed;
        }
        if self.unicode.is_none() {
            self.unicode = previous.unicode;
        }
    }

    fn case_insensitive(&self) -> bool {
        self.case_insensitive.unwrap_or(false)
    }

    fn multi_line(&self) -> bool {
        self.multi_line.unwrap_or(false)
    }

    fn dot_matches_new_line(&self) -> bool {
        self.dot_matches_new_line.unwrap_or(false)
    }

    fn swap_greed(&self) -> bool {
        self.swap_greed.unwrap_or(false)
    }

    fn unicode(&self) -> bool {
        self.unicode.unwrap_or(true)
    }
}

fn hir_ascii_class_unicode(kind: &ast::ClassAsciiKind) -> hir::ClassUnicode {
    let ranges: Vec<_> = ascii_class(kind).iter().cloned().map(|(s, e)| {
        hir::ClassRangeUnicode::new(s, e)
    }).collect();
    hir::ClassUnicode::new(ranges)
}

fn hir_ascii_class_bytes(kind: &ast::ClassAsciiKind) -> hir::ClassBytes {
    let ranges: Vec<_> = ascii_class(kind).iter().cloned().map(|(s, e)| {
        hir::ClassRangeBytes::new(s as u8, e as u8)
    }).collect();
    hir::ClassBytes::new(ranges)
}

fn ascii_class(kind: &ast::ClassAsciiKind) -> &'static [(char, char)] {
    use ast::ClassAsciiKind::*;
    match *kind {
        Alnum => &[('0', '9'), ('A', 'Z'), ('a', 'z')],
        Alpha => &[('A', 'Z'), ('a', 'z')],
        Ascii => &[('\x00', '\x7F')],
        Blank => &[(' ', '\t')],
        Cntrl => &[('\x00', '\x1F'), ('\x7F', '\x7F')],
        Digit => &[('0', '9')],
        Graph => &[('!', '~')],
        Lower => &[('a', 'z')],
        Print => &[(' ', '~')],
        Punct => &[('!', '/'), (':', '@'), ('[', '`'), ('{', '~')],
        Space => &[
            ('\t', '\t'), ('\n', '\n'), ('\x0B', '\x0B'), ('\x0C', '\x0C'),
            ('\r', '\r'), (' ', ' '),
        ],
        Upper => &[('A', 'Z')],
        Word => &[('0', '9'), ('A', 'Z'), ('_', '_'), ('a', 'z')],
        Xdigit => &[('0', '9'), ('A', 'F'), ('a', 'f')],
    }
}

#[cfg(test)]
mod tests {
    use ast::Ast;
    use hir::Hir;
    use parse::Parser;
    use super::{Translator, TranslatorBuilder};

    fn parse(pattern: &str) -> Ast {
        Parser::new().parse(pattern).unwrap()
    }

    fn translate(pattern: &str) -> Hir {
        Translator::new().translate(&parse(pattern)).unwrap()
    }

    fn translate_bytes(pattern: &str) -> Hir {
        TranslatorBuilder::new()
            .allow_invalid_utf8(true)
            .build()
            .translate(&parse(pattern))
            .unwrap()
    }

    #[test]
    fn scratch() {
        let x = translate(r"\p{cyrillic}");
        println!("{:#?}", x);
    }
}

// file: src/lib.rs
// authors: Brandon H. Gomes

//! The Rational Deduction Algorithm

use {
    core::{convert::TryFrom, iter::FromIterator},
    std::vec::Vec,
};

/// Expression Tree
pub trait Expression
where
    Self: Sized,
{
    /// Atomic element type
    type Atom;

    /// Group expression type
    type Group: Default
        + Extend<Self>
        + IntoIterator<Item = Self, IntoIter = Self::GroupIter>
        + FromIterator<Self>;

    /// Iterator type to read from [`Group`]
    ///
    /// [`Group`]: #associatedtype.Group
    type GroupIter: Iterator<Item = Self>;

    /// Convert to [canonical enumeration]
    ///
    /// [canonical enumeration]: enum.Expr.html
    fn cases(self) -> Expr<Self>;

    /// Build an `Expression` from an atomic element.
    fn from_atom(atom: Self::Atom) -> Self;

    /// Build an `Expression` from a grouped expression.
    fn from_group(group: Self::Group) -> Self;

    /// Convert from [canonical enumeration]
    ///
    /// [canonical enumeration]: enum.Expr.html
    fn from_expr(expr: Expr<Self>) -> Self {
        match expr {
            Expr::Atom(atom) => Self::from_atom(atom),
            Expr::Group(group) => Self::from_group(group),
        }
    }

    /// Get default `Expression` from canonical enumeration
    #[inline]
    fn default() -> Self {
        Self::from_expr(Default::default())
    }

    /// Check if expression is an atomic expression.
    #[must_use]
    #[inline]
    fn is_atom(self) -> bool {
        self.cases().is_atom()
    }

    /// Check if expression is a grouped expression.
    #[must_use]
    #[inline]
    fn is_group(self) -> bool {
        self.cases().is_group()
    }

    /// Convert from `Expression` to `Option<Self::Atom>`.
    #[inline]
    fn atom(self) -> Option<Self::Atom> {
        self.cases().atom()
    }

    /// Convert from `Expression` to `Option<Self::Group>`.
    #[inline]
    fn group(self) -> Option<Self::Group> {
        self.cases().group()
    }

    /// Unwrap expression into atomic expression.
    #[must_use]
    #[inline]
    fn unwrap_atom(self) -> Self::Atom {
        self.cases().unwrap_atom()
    }

    /// Unwrap expression into grouped expression.
    #[must_use]
    #[inline]
    fn unwrap_group(self) -> Self::Group {
        self.cases().unwrap_group()
    }

    /// Perform a mapping over the expression.
    #[inline]
    fn map<E, M>(self, m: &M) -> E
    where
        E: Expression,
        M: Map<Self, E>,
    {
        m.on_exprs(self)
    }

    /// Perform a substitution over the expression.
    #[inline]
    fn substitute<E, S>(self, s: &S) -> E
    where
        E: Expression,
        S: Substitution<Self, E>,
    {
        s.on_exprs(self)
    }
}

/// Canonical Concrete Expression Type
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Expr<E>
where
    E: Expression,
{
    /// Atomic element
    Atom(E::Atom),

    /// Grouped expression
    Group(E::Group),
}

impl<E> Expr<E>
where
    E: Expression,
{
    /// Check if expression is an atomic expression.
    #[must_use]
    #[inline]
    pub fn is_atom(&self) -> bool {
        matches!(self, Expr::Atom(_))
    }

    /// Check if expression is a grouped expression.
    #[must_use]
    #[inline]
    pub fn is_group(&self) -> bool {
        matches!(self, Expr::Group(_))
    }

    /// Convert from `Expr` to `Option<E::Atom>`.
    #[inline]
    pub fn atom(self) -> Option<E::Atom> {
        match self {
            Expr::Atom(atom) => Some(atom),
            _ => None,
        }
    }

    /// Convert from `Expr` to `Option<E::Group>`.
    #[inline]
    pub fn group(self) -> Option<E::Group> {
        match self {
            Expr::Group(group) => Some(group),
            _ => None,
        }
    }

    /// Unwrap expression into atomic expression.
    #[must_use]
    #[inline]
    pub fn unwrap_atom(self) -> E::Atom {
        match self {
            Expr::Atom(atom) => atom,
            _ => panic!("called `Expr::atom()` on a `Group` value"),
        }
    }

    /// Unwrap expression into grouped expression.
    #[must_use]
    #[inline]
    pub fn unwrap_group(self) -> E::Group {
        match self {
            Expr::Group(group) => group,
            _ => panic!("called `Expr::group()` on an `Atom` value"),
        }
    }
}

impl<E> Expression for Expr<E>
where
    E: Expression,
{
    type Atom = E::Atom;

    type Group = expr::ExprGroup<E>;

    type GroupIter = expr::ExprGroupIter<E>;

    #[inline]
    fn cases(self) -> Expr<Self> {
        match self {
            Expr::Atom(atom) => Expr::Atom(atom),
            Expr::Group(group) => Expr::Group(expr::ExprGroup { group }),
        }
    }

    #[inline]
    fn from_atom(atom: <Self as Expression>::Atom) -> Self {
        Self::Atom(atom)
    }

    #[inline]
    fn from_group(group: <Self as Expression>::Group) -> Self {
        Self::Group(group.group)
    }
}

impl<E> Default for Expr<E>
where
    E: Expression,
{
    /// Default Expr
    ///
    /// The default expression is the empty group expression.
    fn default() -> Self {
        <Self as Expression>::default()
    }
}

/// Expression Module
pub mod expr {
    use super::*;

    /// Expression Group Container
    pub struct ExprGroup<E>
    where
        E: Expression,
    {
        pub group: E::Group,
    }

    impl<E> Default for ExprGroup<E>
    where
        E: Expression,
    {
        fn default() -> Self {
            ExprGroup {
                group: E::Group::default(),
            }
        }
    }

    impl<E> Extend<Expr<E>> for ExprGroup<E>
    where
        E: Expression,
    {
        fn extend<I>(&mut self, iter: I)
        where
            I: IntoIterator<Item = Expr<E>>,
        {
            self.group.extend(iter.into_iter().map(E::from_expr))
        }
    }

    impl<E> IntoIterator for ExprGroup<E>
    where
        E: Expression,
    {
        type Item = Expr<E>;

        type IntoIter = ExprGroupIter<E>;

        fn into_iter(self) -> Self::IntoIter {
            ExprGroupIter {
                iter: self.group.into_iter(),
            }
        }
    }

    impl<E> FromIterator<Expr<E>> for ExprGroup<E>
    where
        E: Expression,
    {
        fn from_iter<I>(iter: I) -> Self
        where
            I: IntoIterator<Item = Expr<E>>,
        {
            Self {
                group: E::Group::from_iter(iter.into_iter().map(E::from_expr)),
            }
        }
    }

    /// Expression Group Container Iterator
    pub struct ExprGroupIter<E>
    where
        E: Expression,
    {
        iter: E::GroupIter,
    }

    impl<E> Iterator for ExprGroupIter<E>
    where
        E: Expression,
    {
        type Item = Expr<E>;

        fn next(&mut self) -> Option<Self::Item> {
            self.iter.next().map(E::cases)
        }
    }
}

/// Map Trait
pub trait Map<A, B>
where
    A: Expression,
    B: Expression,
{
    /// Compute the map on atoms.
    fn on_atoms(&self, atom: A::Atom) -> B::Atom;

    /// Compute the map on groups.
    fn on_groups(&self, group: A::Group) -> B::Group {
        group.into_iter().map(move |e| self.on_exprs(e)).collect()
    }

    /// Compute the map on expressions.
    fn on_exprs(&self, expr: A) -> B {
        match expr.cases() {
            Expr::Atom(atom) => B::from_atom(self.on_atoms(atom)),
            Expr::Group(group) => B::from_group(self.on_groups(group)),
        }
    }
}

impl<A, B, F> Map<A, B> for F
where
    A: Expression,
    B: Expression,
    F: Fn(A::Atom) -> B::Atom,
{
    fn on_atoms(&self, atom: A::Atom) -> B::Atom {
        self(atom)
    }
}

/// Map from an Iterator
pub trait MapIter<E>
where
    E: Expression,
{
    /// Map term iterator
    type TermIter: Iterator<Item = (E::Atom, E::Atom)>;

    /// Get the map terms.
    fn terms(&self) -> Self::TermIter;

    /// Compute the map on atoms.
    fn on_atoms(&self, atom: E::Atom) -> E::Atom
    where
        E::Atom: PartialEq,
    {
        self.terms()
            .find(|(a, _)| *a == atom)
            .map(move |(_, e)| e)
            .unwrap_or(atom)
    }

    /// Compute the map on groups.
    fn on_groups(&self, group: E::Group) -> E::Group
    where
        E::Atom: PartialEq,
    {
        group.into_iter().map(move |e| self.on_exprs(e)).collect()
    }

    /// Compute the map on expressions.
    fn on_exprs(&self, expr: E) -> E
    where
        E::Atom: PartialEq,
    {
        match expr.cases() {
            Expr::Atom(atom) => E::from_atom(self.on_atoms(atom)),
            Expr::Group(group) => E::from_group(self.on_groups(group)),
        }
    }
}

/// Substitution Trait
pub trait Substitution<A, B>
where
    A: Expression,
    B: Expression,
{
    /// Compute the substitution on atoms.
    fn on_atoms(&self, atom: A::Atom) -> B;

    /// Compute the substitution on groups.
    fn on_groups(&self, group: A::Group) -> B::Group {
        group.into_iter().map(move |e| self.on_exprs(e)).collect()
    }

    /// Compute the substitution on expressions.
    fn on_exprs(&self, expr: A) -> B {
        match expr.cases() {
            Expr::Atom(atom) => self.on_atoms(atom),
            Expr::Group(group) => B::from_group(self.on_groups(group)),
        }
    }
}

impl<A, B, F> Substitution<A, B> for F
where
    A: Expression,
    B: Expression,
    F: Fn(A::Atom) -> B,
{
    fn on_atoms(&self, atom: A::Atom) -> B {
        self(atom)
    }
}

/// Substitution from an Iterator
pub trait SubstitutionIter<E>
where
    E: Expression,
{
    /// Substitution term iterator
    type TermIter: Iterator<Item = (E::Atom, E)>;

    /// Get the substitution terms.
    fn terms(&self) -> Self::TermIter;

    /// Compute the substitution on atoms.
    fn on_atoms(&self, atom: E::Atom) -> E
    where
        E::Atom: PartialEq,
    {
        self.terms()
            .find(|(a, _)| *a == atom)
            .map(move |(_, e)| e)
            .unwrap_or_else(move || E::from_atom(atom))
    }

    /// Compute the substitution on groups.
    fn on_groups(&self, group: E::Group) -> E::Group
    where
        E::Atom: PartialEq,
    {
        group.into_iter().map(move |e| self.on_exprs(e)).collect()
    }

    /// Compute the substitution on expressions.
    fn on_exprs(&self, expr: E) -> E
    where
        E::Atom: PartialEq,
    {
        match expr.cases() {
            Expr::Atom(atom) => self.on_atoms(atom),
            Expr::Group(group) => E::from_group(self.on_groups(group)),
        }
    }
}

/// Compute the symmetric difference of two multisets.
pub fn multiset_symmetric_difference<T, L>(
    left: L,
    right: Vec<T>,
) -> (Vec<T>, impl Iterator<Item = T>)
where
    T: PartialEq,
    L: IntoIterator<Item = T>,
{
    let right_len = right.len();
    let mut matched_indices = Vec::<bool>::with_capacity(right_len);
    matched_indices.resize(right_len, false);
    (
        left.into_iter()
            .filter(|l| {
                (&right).iter().enumerate().all(|(i, r)| {
                    if *l == *r && !matched_indices[i] {
                        matched_indices[i] = true;
                        return false;
                    }
                    true
                })
            })
            .collect(),
        right
            .into_iter()
            .zip(matched_indices)
            .filter_map(move |(r, m)| Some(r).filter(|_| !m)),
    )
}

/// Ratio Trait
pub trait Ratio<T, V>
where
    V: Default + Extend<T> + IntoIterator<Item = T> + FromIterator<T>,
{
    /// Create a new ratio from two base types.
    fn new(top: V, bot: V) -> Self;

    /// Convert to [canonical ratio type]
    ///
    /// [canonical ratio type]: struct.RatioPair.html
    fn cases(self) -> RatioPair<T, V>;

    #[inline]
    fn from_pair(pair: RatioPair<T, V>) -> Self
    where
        Self: Sized,
    {
        Self::new(pair.top, pair.bot)
    }

    /// Get the default ratio.
    #[inline]
    fn default() -> Self
    where
        Self: Sized,
    {
        Self::from_pair(Default::default())
    }

    /// Compose two ratios according to the ratio monoid multiplication algorithm.
    fn pair_compose(top: Self, bot: Self) -> Self
    where
        Self: Sized,
        T: PartialEq,
    {
        let top = top.cases();
        let bot = bot.cases();
        let (mut lower, upper) =
            multiset_symmetric_difference(top.bot, bot.top.into_iter().collect());
        let mut upper: V = upper.collect();
        upper.extend(top.top);
        lower.extend(bot.bot);
        Self::new(upper.into_iter().collect(), lower.into_iter().collect())
    }

    /// Fold a collection of ratios using [`pair_compose`].
    ///
    /// [`pair_compose`]: trait.Ratio.html#method.pair_compose
    fn compose<I>(ratios: I) -> Self
    where
        Self: Sized,
        I: IntoIterator<Item = Self>,
        T: PartialEq,
    {
        let mut iter = ratios.into_iter();
        iter.next()
            .map(move |r| iter.fold(r, Self::pair_compose))
            .unwrap_or_else(Self::default)
    }

    /// Perform a mapping over the ratio.
    fn map<RT, RV, R, M>(self, m: &M) -> R
    where
        Self: Sized,
        T: Expression,
        RT: Expression,
        RV: Default + Extend<RT> + IntoIterator<Item = RT> + FromIterator<RT>,
        R: Ratio<RT, RV>,
        M: Map<T, RT>,
    {
        let ratio = self.cases();
        Ratio::new(
            ratio.top.into_iter().map(|e| m.on_exprs(e)).collect(),
            ratio.bot.into_iter().map(|e| m.on_exprs(e)).collect(),
        )
    }

    /// Perform a substitution over the ratio.
    fn substitute<RT, RV, R, S>(self, s: &S) -> R
    where
        Self: Sized,
        T: Expression,
        RT: Expression,
        RV: Default + Extend<RT> + IntoIterator<Item = RT> + FromIterator<RT>,
        R: Ratio<RT, RV>,
        S: Substitution<T, RT>,
    {
        let ratio = self.cases();
        Ratio::new(
            ratio.top.into_iter().map(|e| s.on_exprs(e)).collect(),
            ratio.bot.into_iter().map(|e| s.on_exprs(e)).collect(),
        )
    }
}

/// Canonical Ratio Type
pub struct RatioPair<T, V>
where
    V: Default + Extend<T> + IntoIterator<Item = T> + FromIterator<T>,
{
    /// Top of the ratio
    pub top: V,

    /// Bottom of the ratio
    pub bot: V,
}

impl<T, V> RatioPair<T, V>
where
    V: Default + Extend<T> + IntoIterator<Item = T> + FromIterator<T>,
{
    /// Reverse a `RatioPair`.
    #[inline]
    pub fn reverse(self) -> Self {
        Self {
            top: self.bot,
            bot: self.top,
        }
    }
}

impl<T, V> Ratio<T, V> for RatioPair<T, V>
where
    V: Default + Extend<T> + IntoIterator<Item = T> + FromIterator<T>,
{
    #[inline]
    fn new(top: V, bot: V) -> Self {
        Self { top, bot }
    }

    #[inline]
    fn cases(self) -> Self {
        self
    }
}

impl<T, V> Default for RatioPair<T, V>
where
    V: Default + Extend<T> + IntoIterator<Item = T> + FromIterator<T>,
{
    #[inline]
    fn default() -> Self {
        Self {
            top: Default::default(),
            bot: Default::default(),
        }
    }
}

impl<E> From<RatioPair<E, E::Group>> for Expr<E>
where
    E: Expression,
{
    fn from(t: RatioPair<E, E::Group>) -> Self {
        let mut group = E::Group::default();
        group.extend(Some(E::from_group(t.top)));
        group.extend(Some(E::from_group(t.bot)));
        Expr::Group(group)
    }
}

/// Conversion from `Expr` to `RatioPair` Error Type
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum RatioPairFromExprError {
    /// The expression is not a group.
    NotGroup,

    /// The expression has the wrong group shape.
    BadGroupShape,

    /// The top element of the group is not a group.
    MissingTopGroup,

    /// The bot element of the group is not a group.
    MissingBotGroup,
}

impl<E> TryFrom<Expr<E>> for RatioPair<E, E::Group>
where
    E: Expression,
{
    type Error = RatioPairFromExprError;

    fn try_from(t: Expr<E>) -> Result<Self, Self::Error> {
        match t {
            Expr::Atom(_) => Err(RatioPairFromExprError::NotGroup),
            Expr::Group(group) => {
                let mut group = group.into_iter();
                if let (Some(top), Some(bot), None) = (group.next(), group.next(), group.next()) {
                    match top.cases() {
                        Expr::Group(top) => match bot.cases() {
                            Expr::Group(bot) => Ok(RatioPair { top, bot }),
                            _ => Err(RatioPairFromExprError::MissingBotGroup),
                        },
                        _ => Err(RatioPairFromExprError::MissingTopGroup),
                    }
                } else {
                    Err(RatioPairFromExprError::BadGroupShape)
                }
            }
        }
    }
}

/// Composition Trait
pub trait Composition<E>
where
    E: Expression + PartialEq,
{
    /// Composition term ratio type.
    type Ratio: Ratio<E, E::Group>;

    /// Composition term substitution type.
    type Substitution: Substitution<E, E>;

    /// Composition term iterator type.
    type TermIter: Iterator<Item = (Self::Ratio, Self::Substitution)>;

    /// Get composition terms.
    fn terms(&self) -> Self::TermIter;

    /// Evaluate the composition.
    fn eval(&self) -> Self::Ratio {
        Ratio::compose(self.terms().map(move |(r, s)| r.substitute(&s)))
    }
}

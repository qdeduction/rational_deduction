// file: src/lib.rs
// authors: Brandon H. Gomes

//! The Rational Deduction Algorithm

use {core::iter::FromIterator, std::vec::Vec};

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
    fn default() -> Self {
        Self::from_expr(Default::default())
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
    /// Check if expression is an atomic expression
    #[must_use]
    pub fn is_atom(&self) -> bool {
        match self {
            Expr::Atom(_) => true,
            _ => false,
        }
    }

    /// Check if expression is a grouped expression
    #[must_use]
    pub fn is_group(&self) -> bool {
        match self {
            Expr::Group(_) => true,
            _ => false,
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

    fn cases(self) -> Expr<Self> {
        match self {
            Expr::Atom(atom) => Expr::Atom(atom),
            Expr::Group(group) => Expr::Group(expr::ExprGroup { group }),
        }
    }

    fn from_atom(atom: <Self as Expression>::Atom) -> Self {
        Self::Atom(atom)
    }

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

    /// Get the top of the ratio.
    fn top(&self) -> V;

    /// Get the bottom of the ratio.
    fn bot(&self) -> V;

    /// Get the default ratio.
    fn default() -> Self
    where
        Self: Sized,
    {
        Self::new(Default::default(), Default::default())
    }

    /// Compose two ratios according to the ratio monoid multiplication algorithm.
    fn pair_compose(top: Self, bot: Self) -> Self
    where
        Self: Sized,
        T: PartialEq,
    {
        let (mut lower, upper) =
            multiset_symmetric_difference(top.bot().into_iter(), bot.top().into_iter().collect());
        let mut upper: V = upper.collect();
        upper.extend(top.top());
        lower.extend(bot.bot());
        Self::new(upper.into_iter().collect(), lower.into_iter().collect())
    }

    /// Fold a collection of ratios using `pair_compose`.
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
}

/// Composition Trait
pub trait Composition<E>
where
    E: Expression + PartialEq,
{
    ///
    ///
    type Ratio: Ratio<E, E::Group>;

    ///
    ///
    type Substitution: Substitution<E, E>;

    ///
    ///
    type TermIter: Iterator<Item = (Self::Ratio, Self::Substitution)>;

    ///
    ///
    fn terms(&self) -> Self::TermIter;

    ///
    ///
    fn eval(&self) -> Self::Ratio {
        Ratio::compose(self.terms().map(move |(r, s)| {
            Ratio::new(
                r.top().into_iter().map(|e| s.on_exprs(e)).collect(),
                r.bot().into_iter().map(|e| s.on_exprs(e)).collect(),
            )
        }))
    }
}

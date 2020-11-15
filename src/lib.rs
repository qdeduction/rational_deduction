// file: src/lib.rs
// authors: Brandon H. Gomes

//! The Rational Deduction Algorithm

use exprz_core::*;

use {
    core::{convert::TryFrom, iter::FromIterator},
    std::vec::Vec,
};

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
        // FIXME: group.into_iter().map(move |e| self.on_exprs(e)).collect()
        let _ = group;
        todo!()
    }

    /// Compute the substitution on expressions.
    fn on_exprs(&self, expr: A) -> B {
        // FIXME:
        // match expr.cases() {
        //     Expr::Atom(atom) => self.on_atoms(atom),
        //     Expr::Group(group) => B::from_group(self.on_groups(group)),
        // }
        let _ = expr;
        todo!()
    }
}

impl<A, B, F> Substitution<A, B> for F
where
    A: Expression,
    B: Expression,
    F: Fn(A::Atom) -> B,
{
    #[inline]
    fn on_atoms(&self, atom: A::Atom) -> B {
        self(atom)
    }
}

/// Generator for substitution using an iterator.
#[inline]
pub fn substitute_iter_on_atoms<'s, E, I>(iter: I, atom: E::Atom) -> E
where
    E: 's + Expression,
    E::Atom: PartialEq,
    I: IntoIterator<Item = (&'s E::Atom, E)>,
{
    iter.into_iter()
        .find(|(a, _)| **a == atom)
        .map(move |(_, t)| t)
        .unwrap_or_else(move || E::from_atom(atom))
}

/// Compute the symmetric difference of two multisets.
pub fn multiset_symmetric_difference<L, OL>(
    left: L,
    right: Vec<L::Item>,
) -> (OL, impl Iterator<Item = L::Item>)
where
    L: IntoIterator,
    L::Item: PartialEq,
    OL: FromIterator<L::Item>,
{
    multiset_symmetric_difference_by(left, right, move |l, r| l == r)
}

/// Compute the symmetric difference of two multisets.
pub fn multiset_symmetric_difference_by<L, OL, F>(
    left: L,
    right: Vec<L::Item>,
    mut eq: F,
) -> (OL, impl Iterator<Item = L::Item>)
where
    L: IntoIterator,
    OL: FromIterator<L::Item>,
    F: FnMut(&L::Item, &L::Item) -> bool,
{
    let right_len = right.len();
    let mut matched_indices = Vec::<bool>::with_capacity(right_len);
    matched_indices.resize(right_len, false);
    (
        left.into_iter()
            .filter(|l| {
                (&right).iter().enumerate().all(|(i, r)| {
                    if eq(l, r) && !matched_indices[i] {
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
    V: IntoIterator<Item = T> + FromIterator<T>,
    Self: Into<RatioPair<T, V>>,
{
    /// Create a new ratio from two base type elements.
    fn new(top: V, bot: V) -> Self;

    /// Convert from a `RatioPair`.
    #[inline]
    fn from_pair(pair: RatioPair<T, V>) -> Self {
        Self::new(pair.top, pair.bot)
    }

    /// Get the default ratio.
    #[inline]
    fn default() -> Self {
        Self::from_pair(Default::default())
    }

    /// Compose two ratios using the ratio monoid multiplication algorithm.
    fn pair_compose(top: Self, bot: Self) -> Self
    where
        T: PartialEq,
    {
        Self::pair_compose_by(top, bot, move |l, r| l == r)
    }

    /// Compose two ratios using the ratio monoid multiplication algorithm.
    fn pair_compose_by<F>(top: Self, bot: Self, mut eq: F) -> Self
    where
        F: FnMut(&T, &T) -> bool,
    {
        let top = top.into();
        let bot = bot.into();
        let (lower, upper) = multiset_symmetric_difference_by::<_, V, _>(
            top.bot,
            bot.top.into_iter().collect(),
            &mut eq,
        );
        Self::new(
            upper.chain(top.top).collect(),
            lower.into_iter().chain(bot.bot).collect(),
        )
    }

    /// Fold a collection of ratios using [`pair_compose`].
    ///
    /// [`pair_compose`]: trait.Ratio.html#method.pair_compose
    fn compose<I>(ratios: I) -> Self
    where
        I: IntoIterator<Item = Self>,
        T: PartialEq,
    {
        Self::compose_by(ratios, move |l, r| l == r)
    }

    /// Fold a collection of ratios using [`pair_compose_by`].
    ///
    /// [`pair_compose_by`]: trait.Ratio.html#method.pair_compose_by
    fn compose_by<I, F>(ratios: I, mut eq: F) -> Self
    where
        I: IntoIterator<Item = Self>,
        F: FnMut(&T, &T) -> bool,
    {
        let mut iter = ratios.into_iter();
        iter.next()
            .map(move |r| iter.fold(r, move |t, b| Self::pair_compose_by(t, b, &mut eq)))
            .unwrap_or_else(Self::default)
    }

    /// Perform a substitution over the ratio.
    fn substitute<F>(self, f: F) -> Self
    where
        T: Expression<Group = V>,
        V: iter::IntoIteratorGen<T>,
        F: FnMut(T::Atom) -> Self,
    {
        let _ratio = self.into();
        let _ = f;
        todo!()
    }
}

/// Canonical Ratio Type
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct RatioPair<T, V>
where
    V: IntoIterator<Item = T> + FromIterator<T>,
{
    /// Top of the ratio
    pub top: V,

    /// Bottom of the ratio
    pub bot: V,
}

impl<T, V> RatioPair<T, V>
where
    V: IntoIterator<Item = T> + FromIterator<T>,
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
    V: IntoIterator<Item = T> + FromIterator<T>,
{
    #[inline]
    fn new(top: V, bot: V) -> Self {
        Self { top, bot }
    }
}

impl<T, V> Default for RatioPair<T, V>
where
    V: IntoIterator<Item = T> + FromIterator<T>,
{
    #[inline]
    fn default() -> Self {
        Self {
            top: V::from_iter(None),
            bot: V::from_iter(None),
        }
    }
}

/// `RatioPair` over an `Expression` type
pub type RatioPairExpr<E> = RatioPair<E, <E as Expression>::Group>;

impl<E> From<RatioPairExpr<E>> for Expr<E>
where
    E: Expression,
    E::Group: IntoIterator<Item = E> + FromIterator<E>,
{
    fn from(ratio: RatioPairExpr<E>) -> Self {
        Self::Group(
            Some(E::from_group(ratio.top))
                .into_iter()
                .chain(Some(E::from_group(ratio.bot)))
                .collect(),
        )
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

    /// The top and bot element of the group are not groups.
    MissingTopBotGroup,
}

impl<E> TryFrom<Expr<E>> for RatioPairExpr<E>
where
    E: Expression,
    E::Group: IntoIterator<Item = E> + FromIterator<E>,
{
    type Error = RatioPairFromExprError;

    fn try_from(expr: Expr<E>) -> Result<Self, Self::Error> {
        match expr {
            Expr::Atom(_) => Err(RatioPairFromExprError::NotGroup),
            Expr::Group(group) => {
                let mut group = group.into_iter();
                if let (Some(top), Some(bot), None) = (group.next(), group.next(), group.next()) {
                    match (top.into(), bot.into()) {
                        (Expr::Group(top), Expr::Group(bot)) => Ok(Self { top, bot }),
                        (_, Expr::Group(_)) => Err(RatioPairFromExprError::MissingTopGroup),
                        (Expr::Group(_), _) => Err(RatioPairFromExprError::MissingBotGroup),
                        _ => Err(RatioPairFromExprError::MissingTopBotGroup),
                    }
                } else {
                    Err(RatioPairFromExprError::BadGroupShape)
                }
            }
        }
    }
}

/// Evaluate a composition by performing each substitution and then composing ratios.
pub fn eval_composition<'t, E, R, S, I>(terms: I) -> R
where
    E: Expression + PartialEq,
    E::Group: IntoIterator<Item = E> + FromIterator<E>,
    R: Ratio<E, E::Group>,
    S: 't + Substitution<E, E>,
    I: IntoIterator<Item = (R, &'t S)>,
{
    let _ = terms;
    // FIXME: Ratio::compose(terms.into_iter().map(move |(r, s)| r.substitute(s)))
    todo!()
}

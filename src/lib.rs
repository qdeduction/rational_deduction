// file: src/lib.rs
// authors: Brandon H. Gomes

//! Rational Deduction

#![forbid(unsafe_code)]
#![no_std]

extern crate alloc;

use {
    core::{convert::TryFrom, iter::FromIterator},
    exprz::{Expr, Expression},
};

/// Package Version
pub const VERSION: &str = env!("CARGO_PKG_VERSION");

/// Ratio Trait
pub trait Ratio<T, V>
where
    V: IntoIterator<Item = T> + FromIterator<T>,
    Self: Into<RatioPair<T, V>>,
{
    /// Create a new ratio from two base type elements.
    fn new(top: V, bot: V) -> Self;

    /// Get reference to top and bottom of ratio.
    fn cases(&self) -> RatioPairRef<'_, T, V>;

    /// Convert from a `RatioPair`.
    #[inline]
    fn from_pair(pair: RatioPair<T, V>) -> Self {
        Self::new(pair.top, pair.bot)
    }

    /// Reverse a `Ratio`.
    #[inline]
    fn reverse(self) -> Self {
        Self::from_pair(self.into().reverse())
    }

    /// Get the default ratio.
    #[inline]
    fn default() -> Self {
        Self::from_pair(Default::default())
    }

    /// Clone a `Ratio`.
    #[inline]
    fn clone(&self) -> Self
    where
        V: Clone,
    {
        let ratio = self.cases();
        Self::new(ratio.top.clone(), ratio.bot.clone())
    }

    /// Check if two `Ratio`s are equal.
    #[inline]
    fn eq<RT, RV, R>(&self, other: &R) -> bool
    where
        R: Ratio<RT, RV>,
        RV: IntoIterator<Item = RT> + FromIterator<RT>,
        V: PartialEq<RV>,
    {
        self.eq_by(other, PartialEq::eq)
    }

    /// Check if two `Ratio`s are equal given the comparison function.
    fn eq_by<RT, RV, R, F>(&self, other: &R, mut eq: F) -> bool
    where
        R: Ratio<RT, RV>,
        RV: IntoIterator<Item = RT> + FromIterator<RT>,
        F: FnMut(&V, &RV) -> bool,
    {
        let lhs = self.cases();
        let rhs = other.cases();
        eq(lhs.top, rhs.top) && eq(lhs.bot, rhs.bot)
    }

    /// Compose two ratios using the ratio monoid multiplication algorithm.
    #[inline]
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
        let (lower, upper) = util::multiset_symmetric_difference_by::<_, V, _>(
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
    #[inline]
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
}

/// Ratio Reference Type
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct RatioPairRef<'v, T, V>
where
    V: IntoIterator<Item = T> + FromIterator<T>,
{
    /// Top of the ratio
    pub top: &'v V,

    /// Bottom of the ratio
    pub bot: &'v V,
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

impl<T, V> Ratio<T, V> for RatioPair<T, V>
where
    V: IntoIterator<Item = T> + FromIterator<T>,
{
    #[inline]
    fn new(top: V, bot: V) -> Self {
        Self { top, bot }
    }

    #[inline]
    fn cases(&self) -> RatioPairRef<'_, T, V> {
        RatioPairRef {
            top: &self.top,
            bot: &self.bot,
        }
    }
}

impl<T, V> Into<RatioPair<T, V>> for (V, V)
where
    V: IntoIterator<Item = T> + FromIterator<T>,
{
    #[inline]
    fn into(self) -> RatioPair<T, V> {
        RatioPair::new(self.0, self.1)
    }
}

impl<T, V> Ratio<T, V> for (V, V)
where
    V: IntoIterator<Item = T> + FromIterator<T>,
{
    #[inline]
    fn new(top: V, bot: V) -> Self {
        (top, bot)
    }

    #[inline]
    fn cases(&self) -> RatioPairRef<'_, T, V> {
        RatioPairRef {
            top: &self.0,
            bot: &self.1,
        }
    }
}

impl<E> From<RatioPair<E, E::Group>> for Expr<E>
where
    E: Expression,
    E::Group: IntoIterator<Item = E> + FromIterator<E>,
{
    /// Convert a `RatioPairExpr<E>` into an `Expr<E>` by forgetting the shape of the underlying
    /// expression.
    #[inline]
    fn from(ratio: RatioPair<E, E::Group>) -> Self {
        Self::Group(
            Some(E::from_group(ratio.top))
                .into_iter()
                .chain(Some(E::from_group(ratio.bot)))
                .collect(),
        )
    }
}

impl<E> TryFrom<Expr<E>> for RatioPair<E, E::Group>
where
    E: Expression,
    E::Group: IntoIterator<Item = E> + FromIterator<E>,
{
    type Error = expr::RatioPairFromExprError;

    /// Parse an `Expr<E>` into a `RatioPairExpr<E>` if it has the correct shape.
    fn try_from(expr: Expr<E>) -> Result<Self, Self::Error> {
        match expr {
            Expr::Atom(_) => Err(expr::RatioPairFromExprError::NotGroup),
            Expr::Group(group) => {
                let mut iter = group.into_iter();
                if let (Some(top), Some(bot), None) = (iter.next(), iter.next(), iter.next()) {
                    match (top.into(), bot.into()) {
                        (Expr::Group(top), Expr::Group(bot)) => Ok(Self { top, bot }),
                        (_, Expr::Group(_)) => Err(expr::RatioPairFromExprError::MissingTopGroup),
                        (Expr::Group(_), _) => Err(expr::RatioPairFromExprError::MissingBotGroup),
                        _ => Err(expr::RatioPairFromExprError::MissingTopBotGroup),
                    }
                } else {
                    Err(expr::RatioPairFromExprError::BadGroupShape)
                }
            }
        }
    }
}

/// Expression Ratio Module
pub mod expr {
    use {
        super::Ratio,
        core::{borrow::Borrow, iter::FromIterator},
        exprz::{iter::IteratorGen, ExprRef, Expression},
    };

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

    /// Check if an `Expression` has the right shape to be a ratio.
    ///
    /// Use [`try_from`] to convert an `Expr<E>` to a `RatioPairExpr<E>`.
    ///
    /// [`try_from`]: ../struct.RatioPair.html#impl-TryFrom<Expr<E>>
    #[must_use]
    pub fn has_ratio_shape<E>(expr: &E) -> bool
    where
        E: Expression,
    {
        match expr.cases() {
            ExprRef::Group(group) => {
                let mut iter = group.iter();
                if let (Some(top), Some(bot), None) = (iter.next(), iter.next(), iter.next()) {
                    top.borrow().is_group() && bot.borrow().is_group()
                } else {
                    false
                }
            }
            _ => false,
        }
    }

    /// Substitute an `Expression` into each `Atom` of `self`.
    #[inline]
    pub fn substitute<E, R, F>(ratio: R, mut f: F) -> R
    where
        E: Expression,
        E::Group: IntoIterator<Item = E> + FromIterator<E>,
        R: Ratio<E, E::Group>,
        F: FnMut(E::Atom) -> E,
    {
        let ratio = ratio.into();
        Ratio::new(
            ratio
                .top
                .into_iter()
                .map(|e| e.substitute(&mut f))
                .collect(),
            ratio
                .bot
                .into_iter()
                .map(|e| e.substitute(&mut f))
                .collect(),
        )
    }

    /// Evaluate a composition by performing each substitution and then composing ratios.
    #[inline]
    pub fn eval_composition<E, R, F, S, I>(terms: I) -> R
    where
        E: Expression + PartialEq,
        E::Group: IntoIterator<Item = E> + FromIterator<E>,
        R: Ratio<E, E::Group>,
        F: FnMut(E::Atom) -> E,
        S: AsMut<F>,
        I: IntoIterator<Item = (R, S)>,
    {
        Ratio::compose(
            terms
                .into_iter()
                .map(move |(r, mut s)| substitute(r, s.as_mut())),
        )
    }
}

/// Utilities
pub mod util {
    use {alloc::vec::Vec, core::iter::FromIterator, exprz::Expression};

    /// Compute the symmetric difference of two multisets.
    #[inline]
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
        // TODO: use bit-vector
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
}

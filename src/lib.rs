//! Rational Deduction
//!
//! _Rust implementation of the rational deduction algorithms_.

// FIXME: reimplement all of the incorrect `derive` traits
// TODO:  implement `Deref/Borrow/ToOwned` traits where possible

#![cfg_attr(docsrs, feature(doc_cfg), forbid(broken_intra_doc_links))]
#![feature(
    associated_type_defaults,
    exhaustive_patterns,
    generic_associated_types
)]
#![allow(incomplete_features)]
#![forbid(missing_docs)]
#![forbid(unsafe_code)]
#![no_std]

extern crate alloc;

use {
    core::{
        convert::{Infallible, TryFrom, TryInto},
        iter::FromIterator,
        marker::PhantomData,
    },
    exprz::{
        shape::{Matcher, Shape},
        Reference as _,
    },
};

/// Package Version
pub const VERSION: &str = env!("CARGO_PKG_VERSION");

/// Crate Prelude Module
pub mod prelude {
    pub use {
        crate::{self as rd, rule::Rule, substitution::Substitution, Structure},
        exprz::{
            self, Expr, ExprRef, Expression, Group, GroupRef, GroupRefItem, GroupRefIter,
            GroupReference, Reference,
        },
    };
}

pub use prelude::*;

/// Container Helper Trait
pub trait Container<T>: FromIterator<T> + IntoIterator<Item = T> {}

impl<T, C> Container<T> for C where C: FromIterator<T> + IntoIterator<Item = T> {}

/// Opaque Container Helper Trait
pub trait OpaqueContainer: FromIterator<Self::Item> + IntoIterator {}

impl<C> OpaqueContainer for C where C: FromIterator<C::Item> + IntoIterator {}

/// Structure Trait
pub trait Structure<E, S>
where
    E: Expression,
    S: Into<Expr<E>> + TryFrom<Expr<E>>,
{
    /// Builds `Self` from the given structure value.
    fn from(structure: S) -> Self;

    /// Extracts the structure value from `self`.
    fn structure(self) -> S;

    /// Converts `self` into an instance of [`Expression`].
    #[inline]
    fn into(self) -> E
    where
        Self: Sized,
    {
        E::from_expr(self.structure().into())
    }

    /// Tries to build `Self` from an instance of [`Expression`].
    #[inline]
    fn try_from(expr: E) -> Result<Self, S::Error>
    where
        Self: Sized,
    {
        expr.into().try_into().map(Self::from)
    }
}

impl<E, S> Structure<E, S> for S
where
    E: Expression,
    S: Into<Expr<E>> + TryFrom<Expr<E>>,
{
    #[inline]
    fn from(structure: S) -> Self {
        structure
    }

    #[inline]
    fn structure(self) -> S {
        self
    }
}

/// Atom-Expr Pairs
///
/// A base structure for [`Substitutions`](Substitution) and `Composition`s.
#[cfg(feature = "aep")]
#[cfg_attr(docsrs, doc(cfg(feature = "aep")))]
pub mod aep {
    use {super::*, alloc::vec::Vec, core::mem};

    /// AEP Pair
    pub type Pair<E> = (<E as Expression>::Atom, E);

    /// AEP Term Reference Type
    #[derive(Clone, Copy, Debug)]
    pub struct TermRef<'e, E>
    where
        E: Expression,
    {
        /// [`Atom`](Expression::Atom) Element
        pub atom: &'e E::Atom,

        /// [`Expression`] Element
        pub expr: &'e E,
    }

    impl<'e, E> TermRef<'e, E>
    where
        E: Expression,
    {
        /// Builds a new AEP term reference.
        #[inline]
        pub fn new(atom: &'e E::Atom, expr: &'e E) -> Self {
            Self { atom, expr }
        }

        /// Returns an owned [`Term`].
        #[inline]
        pub fn to_owned(&self) -> Term<E>
        where
            E::Atom: Clone,
            E::Group: FromIterator<E>,
        {
            Term::new(self.atom.clone(), self.expr.clone())
        }
    }

    impl<'e, E> PartialEq for TermRef<'e, E>
    where
        E: Expression,
        E::Atom: PartialEq,
    {
        #[inline]
        fn eq(&self, other: &Self) -> bool {
            self.atom.eq(other.atom) && self.expr.eq(other.expr)
        }
    }

    impl<'e, E> Eq for TermRef<'e, E>
    where
        E: Expression,
        E::Atom: PartialEq,
    {
    }

    impl<'e, E> From<&'e Term<E>> for TermRef<'e, E>
    where
        E: Expression,
    {
        #[inline]
        fn from(term: &'e Term<E>) -> Self {
            term.as_ref()
        }
    }

    /// AEP Term Type
    #[derive(Debug)]
    pub struct Term<E>
    where
        E: Expression,
    {
        /// [`Atom`](Expression::Atom) Element
        pub atom: E::Atom,

        /// [`Expression`] Element
        pub expr: E,
    }

    impl<E> Term<E>
    where
        E: Expression,
    {
        /// Builds a new AEP term.
        #[inline]
        pub fn new(atom: E::Atom, expr: E) -> Self {
            Self { atom, expr }
        }

        /// Returns the [`&Term`](Term) as a [`TermRef`].
        #[inline]
        pub fn as_ref(&self) -> TermRef<'_, E> {
            TermRef::new(&self.atom, &self.expr)
        }

        /// Flips the term if possible.
        #[inline]
        pub fn flip(self) -> Option<Self> {
            Some(Self::new(self.expr.atom()?, E::from_atom(self.atom)))
        }

        /// Tries the flip the term in place and returns `true` on success.
        ///
        /// # Panics
        ///
        /// This function could panic if the
        /// [`is_atom`](Expression::is_atom)/[`unwrap_atom`](Expression::unwrap_atom) contract is faulty.
        pub fn flip_in_place(&mut self) -> bool
        where
            E::Group: FromIterator<E>,
        {
            if self.expr.is_atom() {
                self.expr = E::from_atom(mem::replace(
                    &mut self.atom,
                    mem::replace(&mut self.expr, E::empty()).unwrap_atom(),
                ));
                true
            } else {
                false
            }
        }

        #[inline]
        fn iter(self) -> impl Iterator<Item = E> {
            util::two_item_iter(E::from_atom(self.atom), self.expr)
        }
    }

    impl<E> Clone for Term<E>
    where
        E: Expression,
        E::Atom: Clone,
        E::Group: FromIterator<E>,
    {
        #[inline]
        fn clone(&self) -> Self {
            Self::new(self.atom.clone(), self.expr.clone())
        }
    }

    impl<E> Copy for Term<E>
    where
        E: Copy + Expression,
        E::Atom: Copy,
        E::Group: FromIterator<E>,
    {
    }

    impl<E> PartialEq for Term<E>
    where
        E: Expression,
        E::Atom: PartialEq,
    {
        #[inline]
        fn eq(&self, other: &Self) -> bool {
            self.as_ref().eq(&other.as_ref())
        }
    }

    impl<E> Eq for Term<E>
    where
        E: Expression,
        E::Atom: PartialEq,
    {
    }

    impl<E> TryFrom<(E, E)> for Term<E>
    where
        E: Expression,
    {
        type Error = ();

        #[inline]
        fn try_from(pair: (E, E)) -> Result<Self, Self::Error> {
            Ok(Self::new(pair.0.atom().ok_or(())?, pair.1))
        }
    }

    impl<E> From<Term<E>> for Pair<E>
    where
        E: Expression,
    {
        #[inline]
        fn from(term: Term<E>) -> Self {
            (term.atom, term.expr)
        }
    }

    /// AEP Structure Type
    #[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
    pub struct Structure<E, V = Vec<Term<E>>>
    where
        E: Expression,
        V: Container<Term<E>>,
    {
        /// AEP terms
        pub terms: V,

        /// Phantom Marker
        __: PhantomData<E>,
    }

    impl<E, V> Structure<E, V>
    where
        E: Expression,
        V: Container<Term<E>>,
    {
        /// Builds a new [`Structure`] from a [`Term`] container.
        #[inline]
        pub fn new(terms: V) -> Self {
            Self {
                terms,
                __: PhantomData,
            }
        }
    }

    impl<E, V> Default for Structure<E, V>
    where
        E: Expression,
        V: Container<Term<E>>,
    {
        #[inline]
        fn default() -> Self {
            Self::new(V::from_iter(None))
        }
    }

    impl<E, V> IntoIterator for Structure<E, V>
    where
        E: Expression,
        V: Container<Term<E>>,
    {
        type Item = Term<E>;

        type IntoIter = <V as IntoIterator>::IntoIter;

        #[inline]
        fn into_iter(self) -> Self::IntoIter {
            self.terms.into_iter()
        }
    }

    impl<E, V> FromIterator<Term<E>> for Structure<E, V>
    where
        E: Expression,
        V: Container<Term<E>>,
    {
        #[inline]
        fn from_iter<I>(iter: I) -> Self
        where
            I: IntoIterator<Item = Term<E>>,
        {
            Self::new(V::from_iter(iter))
        }
    }

    impl<E, V> From<Structure<E, V>> for Expr<E>
    where
        E: Expression,
        E::Group: FromIterator<E>,
        V: Container<Term<E>>,
    {
        #[inline]
        fn from(structure: Structure<E, V>) -> Self {
            Self::Group(structure.into_iter().map(Term::iter).flatten().collect())
        }
    }

    /// AEP Flat Structure Type
    #[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
    pub struct FlatStructure<E, VA = Vec<<E as Expression>::Atom>, VE = Vec<E>>
    where
        E: Expression,
        VA: Container<E::Atom>,
        VE: Container<E>,
    {
        /// AEP [`Atoms`](Expression::Atom)
        pub atoms: VA,

        /// AEP [`Expressions`](Expression)
        pub exprs: VE,

        /// Phantom Marker
        __: PhantomData<E>,
    }

    impl<E, VA, VE> FlatStructure<E, VA, VE>
    where
        E: Expression,
        VA: Container<E::Atom>,
        VE: Container<E>,
    {
        /// Builds a new [`FlatStructure`] from an atom container and an expression container.
        #[inline]
        pub fn new(atoms: VA, exprs: VE) -> Self {
            Self {
                atoms,
                exprs,
                __: PhantomData,
            }
        }
    }

    impl<E, VA, VE> Default for FlatStructure<E, VA, VE>
    where
        E: Expression,
        VA: Container<E::Atom>,
        VE: Container<E>,
    {
        #[inline]
        fn default() -> Self {
            Self::new(VA::from_iter(None), VE::from_iter(None))
        }
    }

    impl<E, VA, VE> IntoIterator for FlatStructure<E, VA, VE>
    where
        E: Expression,
        VA: Container<E::Atom>,
        VE: Container<E>,
    {
        type Item = Pair<E>;

        type IntoIter =
            core::iter::Zip<<VA as IntoIterator>::IntoIter, <VE as IntoIterator>::IntoIter>;

        #[inline]
        fn into_iter(self) -> Self::IntoIter {
            self.atoms.into_iter().zip(self.exprs.into_iter())
        }
    }

    impl<E, VA, VE> FromIterator<Term<E>> for FlatStructure<E, VA, VE>
    where
        E: Expression,
        VA: Container<E::Atom>,
        VE: Container<E>,
    {
        #[inline]
        fn from_iter<I>(iter: I) -> Self
        where
            I: IntoIterator<Item = Term<E>>,
        {
            // FIXME: try to avoid the `Vec` usage if possible
            let (atoms, exprs) = iter
                .into_iter()
                .map(move |t| (t.atom, t.expr))
                .unzip::<_, _, Vec<_>, Vec<_>>();
            Self::new(atoms.into_iter().collect(), exprs.into_iter().collect())
        }
    }

    impl<E, VA, VE> From<FlatStructure<E, VA, VE>> for Expr<E>
    where
        E: Expression,
        E::Group: FromIterator<E>,
        VA: Container<E::Atom>,
        VE: Container<E>,
    {
        #[inline]
        fn from(structure: FlatStructure<E, VA, VE>) -> Self {
            Self::Group(
                structure
                    .into_iter()
                    .map(move |p| Term::new(p.0, p.1).iter())
                    .flatten()
                    .collect(),
            )
        }
    }

    /// AEP Shape Error Type
    #[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
    pub enum ShapeError {
        /// The expression is not a group.
        NotGroup,

        /// The expression is not grouped in pairs.
        NotGroupedInPairs,

        /// The expression does not have the right group shape.
        BadGroupShape(usize),
    }

    /// Checks if an atom matches the `AEP` pattern.
    #[inline]
    pub fn matches_atom<E>(atom: &E::Atom) -> Result<(), ShapeError>
    where
        E: Expression,
    {
        let _ = atom;
        Err(ShapeError::NotGroup)
    }

    /// Checks if a group matches the `AEP` pattern.
    #[inline]
    pub fn matches_group<E>(group: &GroupRef<E>) -> Result<(), ShapeError>
    where
        E: Expression,
    {
        for (i, pair) in util::by_pairs(group.iter()).enumerate() {
            match pair {
                Some((var, _)) => {
                    if !var.is_atom() {
                        return Err(ShapeError::BadGroupShape(i));
                    }
                }
                _ => return Err(ShapeError::NotGroupedInPairs),
            }
        }
        Ok(())
    }

    /// Checks if an expression matches the `AEP` pattern.
    #[inline]
    pub fn matches<E>(expr: &ExprRef<E>) -> Result<(), ShapeError>
    where
        E: Expression,
    {
        match expr {
            ExprRef::Atom(atom) => matches_atom::<E>(atom),
            ExprRef::Group(group) => matches_group::<E>(group),
        }
    }

    impl<E, V> Matcher<E> for Structure<E, V>
    where
        E: Expression,
        V: Container<Term<E>>,
    {
        type Error = ShapeError;

        #[inline]
        fn matches_atom(atom: &E::Atom) -> Result<(), Self::Error> {
            matches_atom::<E>(atom)
        }

        #[inline]
        fn matches_group(group: GroupRef<E>) -> Result<(), Self::Error> {
            matches_group::<E>(&group)
        }
    }
}

/// Rule Module
pub mod rule {
    use super::*;

    /// Composes two rules using the ratio monoid multiplication algorithm.
    pub fn pair_compose_by<E, T, B, Output, F>(top: T, bot: B, eq: F) -> Output
    where
        E: Expression,
        E::Group: Container<E>,
        T: Rule<E>,
        B: Rule<E>,
        Output: Rule<E>,
        F: FnMut(&E, &E) -> bool,
    {
        let top = top.structure();
        let bot = bot.structure();
        let (lower, upper) = util::multiset_symmetric_difference_by::<_, _, _, E::Group>(
            top.bot,
            bot.top.into_iter().collect(),
            eq,
        );
        Output::from(Structure::new(
            upper.chain(top.top).collect(),
            lower.into_iter().chain(bot.bot).collect(),
        ))
    }

    /// Composes two rules using the ratio monoid multiplication algorithm.
    #[inline]
    pub fn pair_compose<E, T, B, Output>(top: T, bot: B) -> Output
    where
        E: Expression,
        E::Atom: PartialEq,
        E::Group: Container<E>,
        T: Rule<E>,
        B: Rule<E>,
        Output: Rule<E>,
    {
        pair_compose_by(top, bot, E::eq)
    }

    /// Fold an iterator of rules using [`pair_compose_by`].
    #[inline]
    pub fn compose_by<E, R, I, F>(rules: I, mut eq: F) -> R
    where
        E: Expression,
        E::Group: Container<E>,
        R: Rule<E>,
        I: IntoIterator<Item = R>,
        F: FnMut(&E, &E) -> bool,
    {
        rules
            .into_iter()
            .reduce(move |t, b| pair_compose_by(t, b, &mut eq))
            .unwrap_or_else(R::empty)
    }

    /// Fold an iterator of rules using [`pair_compose`].
    #[inline]
    pub fn compose<E, R, I>(rules: I) -> R
    where
        E: Expression,
        E::Atom: PartialEq,
        E::Group: Container<E>,
        R: Rule<E>,
        I: IntoIterator<Item = R>,
    {
        compose_by(rules, E::eq)
    }

    /// Parallel [`Rule`] Algorithms
    #[cfg(feature = "parallel")]
    #[cfg_attr(docsrs, doc(cfg(feature = "parallel")))]
    pub mod parallel {
        use {
            super::*,
            crate::util::parallel::ParallelContainer,
            rayon::iter::{IntoParallelIterator, ParallelIterator},
        };

        /// Composes two rules using the ratio monoid multiplication algorithm.
        #[inline]
        pub fn pair_compose_by<E, T, B, Output, F>(top: T, bot: B, eq: F) -> Output
        where
            E: Expression + Send + Sync,
            E::Group: Container<E> + ParallelContainer<E>,
            T: Rule<E>,
            B: Rule<E>,
            Output: Rule<E>,
            F: Send + Sync + Fn(&E, &E) -> bool,
        {
            let top = top.structure();
            let bot = bot.structure();
            let (lower, upper) = util::parallel::multiset_symmetric_difference_by::<
                _,
                _,
                _,
                E::Group,
            >(top.bot, bot.top.into_iter().collect(), eq);
            Output::from(super::Structure::new(
                upper.chain(top.top).collect(),
                lower.into_iter().chain(bot.bot).collect(),
            ))
        }

        /// Composes two rules using the ratio monoid multiplication algorithm.
        #[inline]
        pub fn pair_compose<E, T, B, Output>(top: T, bot: B) -> Output
        where
            E: Expression + Send + Sync,
            E::Atom: PartialEq,
            E::Group: Container<E> + ParallelContainer<E>,
            for<'g> GroupRef<'g, E>: exprz::IndexedParallelGroupReference<E>,
            T: Rule<E>,
            B: Rule<E>,
            Output: Rule<E>,
        {
            pair_compose_by(top, bot, E::parallel_eq)
        }

        /// Fold an iterator of rules using [`pair_compose_by`].
        #[inline]
        pub fn compose_by<E, R, I, F>(rules: I, eq: F) -> R
        where
            E: Expression + Send + Sync,
            E::Group: Container<E> + ParallelContainer<E>,
            for<'g> GroupRef<'g, E>: exprz::IndexedParallelGroupReference<E>,
            R: Rule<E> + Send + Sync,
            I: IntoParallelIterator<Item = R>,
            F: Send + Sync + Fn(&E, &E) -> bool,
        {
            rules
                .into_par_iter()
                .reduce(R::empty, move |t, b| pair_compose_by(t, b, &eq))
        }

        /// Fold an iterator of rules using [`pair_compose`].
        #[inline]
        pub fn compose<E, R, I>(rules: I) -> R
        where
            E: Expression + Send + Sync,
            E::Atom: PartialEq,
            E::Group: Container<E> + ParallelContainer<E>,
            for<'g> GroupRef<'g, E>: exprz::IndexedParallelGroupReference<E>,
            R: Rule<E> + Send + Sync,
            I: IntoParallelIterator<Item = R>,
        {
            compose_by(rules, E::parallel_eq)
        }
    }

    /// Returns `true` if the two ratios are equal pointwise.
    #[inline]
    pub fn eq<'e, E>(
        lhs_top: &GroupRef<'e, E>,
        lhs_bot: &GroupRef<'e, E>,
        rhs_top: &GroupRef<'e, E>,
        rhs_bot: &GroupRef<'e, E>,
    ) -> bool
    where
        E: Expression,
        E::Atom: PartialEq,
    {
        ExprRef::<E>::eq_groups::<E>(lhs_top, rhs_top)
            && ExprRef::<E>::eq_groups::<E>(lhs_bot, rhs_bot)
    }

    /// Rule Trait
    // TODO: `eq_by_symmetric_cancellation`
    // TODO: `has_cancellation`
    // TODO: `has_intersection`
    pub trait Rule<E>: super::Structure<E, Structure<E>>
    where
        E: Expression,
        E::Group: Container<E>,
    {
        /// Transforms `&self` into the appropriate reference structure.
        fn cases(&self) -> Reference<E>;

        /// Returns a reference to the top element of the rule.
        #[inline]
        fn top(&self) -> GroupRef<E> {
            self.cases().top
        }

        /// Returns a reference to the bottom element of the rule.
        #[inline]
        fn bot(&self) -> GroupRef<E> {
            self.cases().bot
        }

        /// Returns `true` if the two rules are equal pointwise.
        #[inline]
        fn eq<R>(&self, other: &R) -> bool
        where
            E::Atom: PartialEq,
            R: Rule<E>,
        {
            self.cases().eq(&other.cases())
        }

        /// Clones a [`Rule`].
        #[inline]
        fn clone(&self) -> Self
        where
            Self: Sized,
            E::Atom: Clone,
        {
            Self::from(Clone::clone(&Structure::from(self.cases())))
        }

        /// Builds a new [`Rule`] from two groups.
        #[inline]
        fn new(top: E::Group, bot: E::Group) -> Self
        where
            Self: Sized,
        {
            Self::from(Structure::new(top, bot))
        }

        /// Builds an empty [`Rule`].
        #[inline]
        fn empty() -> Self
        where
            Self: Sized,
        {
            Self::from(Default::default())
        }

        /// Returns the top and bottom element of the rule as a pair.
        #[inline]
        fn pair(self) -> Pair<E>
        where
            Self: Sized,
        {
            self.structure().pair()
        }

        /// Returns the top and bottom element of the rule as a pair.
        #[inline]
        fn ref_pair(&self) -> RefPair<E> {
            self.cases().ref_pair()
        }

        /// Performs substitution over the rule.
        #[inline]
        fn substitute<S>(self, substitution: &S) -> Self
        where
            Self: Sized,
            E::Atom: Clone + PartialEq,
            S: Substitution<E>,
        {
            // TODO: what about more general substitution methods (see `Expression::substitute`)
            let (top, bot) = self.pair();
            Self::new(substitution.apply_group(top), substitution.apply_group(bot))
        }

        /// Performs substitution over the rule by reference.
        #[inline]
        fn substitute_ref<S>(&self, substitution: &S) -> Self
        where
            Self: Sized,
            E::Atom: Clone + PartialEq,
            S: Substitution<E>,
        {
            // TODO: what about more general substitution methods (see `Expression::substitute_ref`)
            Self::new(
                substitution.apply_group_ref(&self.top()),
                substitution.apply_group_ref(&self.bot()),
            )
        }
    }

    /// [`Rule`] Reference Structure Type
    pub struct Reference<'e, E>
    where
        E: 'e + Expression,
    {
        /// Top element of the rule
        pub top: GroupRef<'e, E>,

        /// Bottom element of the rule
        pub bot: GroupRef<'e, E>,
    }

    impl<'e, E> Reference<'e, E>
    where
        E: Expression,
    {
        /// Builds a new [`Reference`] from references to the top and bottom of a rule.
        #[inline]
        pub fn new(top: GroupRef<'e, E>, bot: GroupRef<'e, E>) -> Self {
            Self { top, bot }
        }

        /// Returns the top and bottom element of the rule as a pair.
        #[inline]
        pub fn ref_pair(self) -> RefPair<'e, E> {
            (self.top, self.bot)
        }

        /// Returns the top and bottom element of the rule as a pair.
        #[inline]
        pub fn ref_pair_by_ref(&self) -> (&GroupRef<'e, E>, &GroupRef<'e, E>) {
            (&self.top, &self.bot)
        }
    }

    impl<'e, E> Clone for Reference<'e, E>
    where
        E: Expression,
        GroupRef<'e, E>: Clone,
    {
        #[inline]
        fn clone(&self) -> Self {
            Self::new(self.top.clone(), self.bot.clone())
        }
    }

    impl<'e, E> Copy for Reference<'e, E>
    where
        E: Expression,
        GroupRef<'e, E>: Copy,
    {
    }

    impl<'e, E> Eq for Reference<'e, E>
    where
        E: Expression,
        E::Atom: PartialEq,
    {
    }

    impl<'e, E> PartialEq for Reference<'e, E>
    where
        E: Expression,
        E::Atom: PartialEq,
    {
        #[inline]
        fn eq(&self, other: &Self) -> bool {
            eq::<E>(&self.top, &self.bot, &other.top, &other.bot)
        }
    }

    impl<'e, E> From<&'e Structure<E>> for Reference<'e, E>
    where
        E: Expression,
    {
        #[inline]
        fn from(structure: &'e Structure<E>) -> Self {
            Self::new(structure.top.as_ref(), structure.bot.as_ref())
        }
    }

    /// Based [`Rule`] Reference Structure Type
    pub struct BasedReference<'e, E>
    where
        E: 'e + Expression,
    {
        /// Base [`Group`](Expression::Group) Reference
        pub base: GroupRef<'e, E>,
    }

    impl<'e, E> BasedReference<'e, E>
    where
        E: Expression,
    {
        /// Builds a new [`BasedReference`] from a base group reference.
        ///
        /// # Safety
        ///
        /// This function does not perform any checks to ensure that the [`base`](Self::base)
        /// group reference points to a valid [`Rule`] structure. The [`top`](Self::top) and
        /// [`bot`](Self::bot) methods will panic if the [`base`](Self::base) reference is not valid.
        ///
        /// Use [`new`](Self::new) to build a [`BasedReference`] with a valid base reference.
        #[inline]
        pub fn new_unchecked(base: GroupRef<'e, E>) -> Self {
            Self { base }
        }

        /// Builds a new [`BasedReference`] from a base group reference.
        #[inline]
        pub fn new(base: GroupRef<'e, E>) -> Result<Self, GroupRef<'e, E>> {
            if Self::is_valid_base_reference(&base) {
                Ok(Self::new_unchecked(base))
            } else {
                Err(base)
            }
        }

        /// Returns `true` if [`base`](Self::base) is a valid [`Rule`] reference.
        #[inline]
        pub fn is_valid_base_reference(base: &GroupRef<'e, E>) -> bool {
            let mut iter = base.iter();
            iter.next()
                .map(exprz::Reference::is_group)
                .zip(iter.next().map(exprz::Reference::is_group))
                .map(move |(t, b)| t && b)
                .unwrap_or(false)
        }

        /// Returns `true` if [`self.base`](Self::base) is a valid [`Rule`] reference.
        #[inline]
        pub fn is_valid(&self) -> bool {
            Self::is_valid_base_reference(&self.base)
        }

        /// Returns the top element of the rule.
        ///
        /// # Panics
        ///
        /// This function panics if the [`base`](Self::base) reference does not point to a valid rule object.
        #[inline]
        pub fn top(&self) -> GroupRef<E> {
            self.ref_pair().0
        }

        /// Tries to return the top element of the rule. Return `None` if
        /// [`self.base`](Self::base) is an invalid [`Rule`] reference.
        #[inline]
        pub fn try_top(&self) -> Option<GroupRef<E>> {
            // TODO: return a more informative `Result<_, _>`
            self.try_ref_pair().map(move |p| p.0)
        }

        /// Returns the bottom element of the rule.
        ///
        /// # Panics
        ///
        /// This function panics if the [`base`](Self::base) reference does not point to a valid rule object.
        #[inline]
        pub fn bot(&self) -> GroupRef<E> {
            self.ref_pair().1
        }

        /// Tries to return the bottom element of the rule. Return `None` if
        /// [`self.base`](Self::base) is an invalid [`Rule`] reference.
        #[inline]
        pub fn try_bot(&self) -> Option<GroupRef<E>> {
            // TODO: return a more informative `Result<_, _>`
            self.try_ref_pair().map(move |p| p.1)
        }

        /// Returns the top and bottom element of the rule as a pair.
        ///
        /// # Panics
        ///
        /// This function panics if the [`base`](Self::base) reference does not point to a valid rule object.
        #[inline]
        pub fn ref_pair(&self) -> RefPair<E> {
            // FIXME: use `unwrap_unchecked` when it comes out
            let mut iter = self.base.iter();
            (
                iter.next().unwrap().unwrap_group(),
                iter.next().unwrap().unwrap_group(),
            )
        }

        /// Tries to return the top and bottom element of the rule as a pair. Returns `None` if
        /// [`self.base`](Self::base) is an invalid [`Rule`] reference.
        #[inline]
        pub fn try_ref_pair(&self) -> Option<RefPair<E>> {
            // TODO: return a more informative `Result<_, _>`
            let mut iter = self.base.iter();
            iter.next()
                .and_then(exprz::Reference::group)
                .zip(iter.next().and_then(exprz::Reference::group))
        }
    }

    impl<'e, E> Clone for BasedReference<'e, E>
    where
        E: Expression,
        GroupRef<'e, E>: Clone,
    {
        #[inline]
        fn clone(&self) -> Self {
            Self::new_unchecked(self.base.clone())
        }
    }

    impl<'e, E> Copy for BasedReference<'e, E>
    where
        E: Expression,
        GroupRef<'e, E>: Copy,
    {
    }

    impl<'e, E> Eq for BasedReference<'e, E>
    where
        E: Expression,
        E::Atom: PartialEq,
    {
    }

    impl<'e, E> PartialEq for BasedReference<'e, E>
    where
        E: Expression,
        E::Atom: PartialEq,
    {
        #[inline]
        fn eq(&self, other: &Self) -> bool {
            eq::<E>(&self.top(), &self.bot(), &other.top(), &other.bot())
        }
    }

    impl<'e, E> TryFrom<ExprRef<'e, E>> for BasedReference<'e, E>
    where
        E: Expression,
    {
        type Error = <Structure<E> as Matcher<E>>::Error;

        #[inline]
        fn try_from(expr: ExprRef<'e, E>) -> Result<Self, Self::Error> {
            matches(&expr)?;
            Ok(Self::new_unchecked(expr.unwrap_group()))
        }
    }

    /// [`Rule`] Structure Type
    #[derive(Debug)]
    pub struct Structure<E>
    where
        E: Expression,
    {
        /// Top element of the rule
        pub top: E::Group,

        /// Bottom element of the rule
        pub bot: E::Group,
    }

    impl<E> Structure<E>
    where
        E: Expression,
    {
        /// Builds a new [`Structure`] from a pair of groups.
        #[inline]
        pub fn new(top: E::Group, bot: E::Group) -> Self {
            Self { top, bot }
        }

        /// Returns the [`Structure`] as a [`Pair`].
        #[inline]
        pub fn pair(self) -> Pair<E> {
            (self.top, self.bot)
        }

        /// Returns the [`Structure`] as a pair of references.
        #[inline]
        pub fn pair_by_ref(&self) -> (&E::Group, &E::Group) {
            (&self.top, &self.bot)
        }
    }

    impl<E> Clone for Structure<E>
    where
        E: Expression,
        E::Atom: Clone,
        E::Group: FromIterator<E>,
    {
        #[inline]
        fn clone(&self) -> Self {
            Reference::from(self).into()
        }
    }

    impl<E> Copy for Structure<E>
    where
        E: Expression,
        E::Atom: Clone,
        E::Group: Copy + FromIterator<E>,
    {
    }

    impl<E> Default for Structure<E>
    where
        E: Expression,
        E::Group: FromIterator<E>,
    {
        #[inline]
        fn default() -> Self {
            Self::new(E::Group::empty(), E::Group::empty())
        }
    }

    impl<E> Eq for Structure<E>
    where
        E: Expression,
        E::Atom: PartialEq,
    {
    }

    impl<E> PartialEq for Structure<E>
    where
        E: Expression,
        E::Atom: PartialEq,
    {
        #[inline]
        fn eq(&self, other: &Self) -> bool {
            Reference::from(self).eq(&other.into())
        }
    }

    impl<'e, E> From<Reference<'e, E>> for Structure<E>
    where
        E: Expression,
        E::Atom: Clone,
        E::Group: FromIterator<E>,
    {
        #[must_use]
        #[inline]
        fn from(reference: Reference<'e, E>) -> Self {
            Self::new(reference.top.to_owned(), reference.bot.to_owned())
        }
    }

    impl<'e, E> From<BasedReference<'e, E>> for Structure<E>
    where
        E: Expression,
        E::Atom: Clone,
        E::Group: FromIterator<E>,
    {
        #[must_use]
        #[inline]
        fn from(reference: BasedReference<'e, E>) -> Self {
            Self::new(reference.top().to_owned(), reference.bot().to_owned())
        }
    }

    impl<E> From<Structure<E>> for Expr<E>
    where
        E: Expression,
        E::Group: FromIterator<E>,
    {
        #[must_use]
        #[inline]
        fn from(structure: Structure<E>) -> Self {
            Self::Group(
                util::two_item_iter(structure.top, structure.bot)
                    .map(E::from_group)
                    .collect(),
            )
        }
    }

    /// [`Rule`] Shape Error Type
    #[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
    pub enum ShapeError {
        /// The expression is not a group.
        NotGroup,

        /// The expression has the wrong group shape.
        BadGroupShape,

        /// The `top` element of the group is not a group.
        MissingTopGroup,

        /// The `bot` element of the group is not a group.
        MissingBotGroup,

        /// The `top` and `bot` element of the group are not groups.
        MissingTopBotGroups,
    }

    /// Checks if an atom matches the [`Rule`] pattern.
    #[inline]
    pub fn matches_atom<E>(atom: &E::Atom) -> Result<(), ShapeError>
    where
        E: Expression,
    {
        let _ = atom;
        Err(ShapeError::NotGroup)
    }

    /// Checks if a group matches the [`Rule`] pattern.
    #[inline]
    pub fn matches_group<E>(group: &GroupRef<E>) -> Result<(), ShapeError>
    where
        E: Expression,
    {
        let mut iter = group.iter();
        match (
            iter.next().map(super::Reference::is_group),
            iter.next().map(super::Reference::is_group),
            iter.next(),
        ) {
            (Some(top), Some(bot), None) => match (top, bot) {
                (true, true) => Ok(()),
                (true, false) => Err(ShapeError::MissingBotGroup),
                (false, true) => Err(ShapeError::MissingTopGroup),
                _ => Err(ShapeError::MissingTopBotGroups),
            },
            _ => Err(ShapeError::BadGroupShape),
        }
    }

    /// Checks if an expression matches the [`Rule`] pattern.
    #[inline]
    pub fn matches<E>(expr: &ExprRef<E>) -> Result<(), ShapeError>
    where
        E: Expression,
    {
        match expr {
            ExprRef::Atom(atom) => matches_atom::<E>(atom),
            ExprRef::Group(group) => matches_group::<E>(group),
        }
    }

    impl<E> Matcher<E> for Structure<E>
    where
        E: Expression,
    {
        type Error = ShapeError;

        #[inline]
        fn matches_atom(atom: &E::Atom) -> Result<(), Self::Error> {
            matches_atom::<E>(atom)
        }

        #[inline]
        fn matches_group(group: GroupRef<E>) -> Result<(), Self::Error> {
            matches_group::<E>(&group)
        }
    }

    impl<E> TryFrom<Expr<E>> for Structure<E>
    where
        E: Expression,
        E::Group: IntoIterator<Item = E>,
    {
        type Error = <Structure<E> as Matcher<E>>::Error;

        fn try_from(expr: Expr<E>) -> Result<Self, Self::Error> {
            match expr.group() {
                Some(group) => {
                    let mut iter = group.into_iter();
                    match (iter.next(), iter.next(), iter.next()) {
                        (Some(top), Some(bot), None) => match (top.group(), bot.group()) {
                            (Some(top), Some(bot)) => Ok(Self::new(top, bot)),
                            (_, Some(_)) => Err(Self::Error::MissingTopGroup),
                            (Some(_), _) => Err(Self::Error::MissingBotGroup),
                            _ => Err(Self::Error::MissingTopBotGroups),
                        },
                        _ => Err(Self::Error::BadGroupShape),
                    }
                }
                _ => Err(Self::Error::NotGroup),
            }
        }
    }

    impl<E> Shape<E> for Structure<E>
    where
        E: Expression,
        E::Group: Container<E>,
    {
    }

    impl<E> Rule<E> for Structure<E>
    where
        E: Expression,
        E::Group: Container<E>,
    {
        #[inline]
        fn cases(&self) -> Reference<E> {
            self.into()
        }
    }

    /// [`Rule`] Reference Pair Type
    pub type RefPair<'e, E> = (GroupRef<'e, E>, GroupRef<'e, E>);

    /// [`Rule`] Pair Type
    pub type Pair<E> = (<E as Expression>::Group, <E as Expression>::Group);
}

/// Substitution Module
pub mod substitution {
    use {
        super::*,
        alloc::vec::Vec,
        core::{iter, mem, slice},
    };

    /// Returns the corresponding expression from the substitution iterator.
    #[inline]
    pub fn get_expression<'s, E, I>(iter: I, atom: &E::Atom) -> Option<E>
    where
        E: 's + Expression,
        E::Atom: PartialEq,
        I: IntoIterator<Item = (&'s E::Atom, E)>,
    {
        iter.into_iter()
            .find(move |(a, _)| *a == atom)
            .map(move |(_, t)| t)
    }

    #[inline]
    fn from_iter_on_atoms_inner<'s, E, I>(iter: &mut I, atom: E::Atom) -> E
    where
        E: 's + Expression,
        E::Atom: PartialEq,
        I: Iterator<Item = (&'s E::Atom, E)>,
    {
        get_expression(iter, &atom).unwrap_or_else(move || E::from_atom(atom))
    }

    #[inline]
    fn from_iter_on_atoms_ref_inner<'s, E, I>(iter: &mut I, atom: &E::Atom) -> E
    where
        E: 's + Expression,
        E::Atom: Clone + PartialEq,
        I: Iterator<Item = (&'s E::Atom, E)>,
    {
        get_expression(iter, atom).unwrap_or_else(move || E::from_atom(atom.clone()))
    }

    /// Performs a substitution using data from an iterator to an atomic expression.
    #[inline]
    pub fn from_iter_on_atoms<'s, E, I>(iter: I, atom: E::Atom) -> E
    where
        E: 's + Expression,
        E::Atom: PartialEq,
        I: IntoIterator<Item = (&'s E::Atom, E)>,
    {
        from_iter_on_atoms_inner(&mut iter.into_iter(), atom)
    }

    /// Performs a substitution by reference using data from an iterator to an atomic expression.
    #[inline]
    pub fn from_iter_on_atoms_ref<'s, E, I>(iter: I, atom: &E::Atom) -> E
    where
        E: 's + Expression,
        E::Atom: Clone + PartialEq,
        I: IntoIterator<Item = (&'s E::Atom, E)>,
    {
        from_iter_on_atoms_ref_inner(&mut iter.into_iter(), atom)
    }

    /// Returns a function which performs substitution using data from an iterator to an atomic expression.
    #[inline]
    pub fn from_iter_on_atoms_fn<'s, E, I>(iter: I) -> impl FnMut(E::Atom) -> E
    where
        E: 's + Expression,
        E::Atom: PartialEq,
        I: IntoIterator<Item = (&'s E::Atom, E)>,
    {
        let mut iter = iter.into_iter();
        move |atom| from_iter_on_atoms_inner(&mut iter, atom)
    }

    /// Returns a function which performs substitution by reference using data from an iterator to an atomic expression.
    #[inline]
    pub fn from_iter_on_atoms_ref_fn<'s, E, I>(iter: I) -> impl FnMut(&E::Atom) -> E
    where
        E: 's + Expression,
        E::Atom: Clone + PartialEq,
        I: IntoIterator<Item = (&'s E::Atom, E)>,
    {
        let mut iter = iter.into_iter();
        move |atom| from_iter_on_atoms_ref_inner(&mut iter, atom)
    }

    /// Performs substitution using data from an iterator.
    #[inline]
    pub fn from_iter<'s, E, I>(iter: I, expr: E) -> E
    where
        E: 's + Expression,
        E::Atom: PartialEq,
        E::Group: Container<E>,
        I: IntoIterator<Item = (&'s E::Atom, E)>,
    {
        expr.substitute(from_iter_on_atoms_fn(iter))
    }

    /// Performs substitution by reference using data from an iterator.
    #[inline]
    pub fn from_iter_ref<'s, E, I>(iter: I, expr: &E) -> E
    where
        E: 's + Expression,
        E::Atom: Clone + PartialEq,
        E::Group: FromIterator<E>,
        I: IntoIterator<Item = (&'s E::Atom, E)>,
    {
        expr.substitute_ref(from_iter_on_atoms_ref_fn(iter))
    }

    /// Returns a function which performs substitution using data from an iterator.
    #[inline]
    pub fn from_iter_fn<'s, E, I>(iter: I) -> impl FnOnce(E) -> E
    where
        E: 's + Expression,
        E::Atom: PartialEq,
        E::Group: Container<E>,
        I: IntoIterator<Item = (&'s E::Atom, E)>,
    {
        move |expr| from_iter(iter, expr)
    }

    /// Returns a function which performs substitution by reference using data from an iterator.
    #[inline]
    pub fn from_iter_ref_fn<'s, E, I>(iter: I) -> impl FnOnce(&E) -> E
    where
        E: 's + Expression,
        E::Atom: Clone + PartialEq,
        E::Group: FromIterator<E>,
        I: IntoIterator<Item = (&'s E::Atom, E)>,
    {
        move |expr| from_iter_ref(iter, expr)
    }

    /// Substitution Term Reference Type
    #[derive(Clone, Copy, Debug)]
    pub struct TermRef<'e, E>
    where
        E: Expression,
    {
        /// Substitution variable atom
        pub var: &'e E::Atom,

        /// Substitution expression
        pub expr: &'e E,
    }

    impl<'e, E> TermRef<'e, E>
    where
        E: Expression,
    {
        /// Builds a new substitution term reference.
        #[inline]
        pub fn new(var: &'e E::Atom, expr: &'e E) -> Self {
            Self { var, expr }
        }

        /// Checks if `&self` is the identity substitution.
        #[inline]
        pub fn is_identity(&self) -> bool
        where
            E::Atom: PartialEq,
        {
            self.expr.atom().map_or(false, move |atom| atom == self.var)
        }

        /// Returns an owned [`Term`].
        #[inline]
        pub fn to_owned(&self) -> Term<E>
        where
            E::Atom: Clone,
            E::Group: FromIterator<E>,
        {
            Term::new(self.var.clone(), self.expr.clone())
        }
    }

    impl<'e, E> PartialEq for TermRef<'e, E>
    where
        E: Expression,
        E::Atom: PartialEq,
    {
        #[inline]
        fn eq(&self, other: &Self) -> bool {
            self.var.eq(other.var) && self.expr.eq(other.expr)
        }
    }

    impl<'e, E> Eq for TermRef<'e, E>
    where
        E: Expression,
        E::Atom: PartialEq,
    {
    }

    impl<'e, E> From<&'e Term<E>> for TermRef<'e, E>
    where
        E: Expression,
    {
        #[inline]
        fn from(term: &'e Term<E>) -> Self {
            term.as_ref()
        }
    }

    /// Substitution Term Type
    #[derive(Debug)]
    pub struct Term<E>
    where
        E: Expression,
    {
        /// Substitution variable atom
        pub var: E::Atom,

        /// Substitution expression
        pub expr: E,
    }

    impl<E> Term<E>
    where
        E: Expression,
    {
        /// Builds a new substitution term.
        #[inline]
        pub fn new(var: E::Atom, expr: E) -> Self {
            Self { var, expr }
        }

        /// Returns the [`&Term`](Term) as a [`TermRef`].
        #[inline]
        pub fn as_ref(&self) -> TermRef<'_, E> {
            TermRef::new(&self.var, &self.expr)
        }

        /// Builds an identity [`Term`].
        #[inline]
        pub fn identity(atom: E::Atom) -> Self
        where
            E::Atom: Clone,
        {
            Self::new(atom.clone(), E::from_atom(atom))
        }

        /// Checks if `&self` is the identity substitution.
        #[inline]
        pub fn is_identity(&self) -> bool
        where
            E::Atom: PartialEq,
        {
            self.as_ref().is_identity()
        }

        /// Flips the substitution if possible.
        #[inline]
        pub fn flip(self) -> Option<Self> {
            Some(Self::new(self.expr.atom()?, E::from_atom(self.var)))
        }

        /// Tries the flip the substitution in place and returns `true` on success.
        ///
        /// # Panics
        ///
        /// This function could panic if the `is_atom`/`unwrap_atom` contract is faulty.
        pub fn flip_in_place(&mut self) -> bool
        where
            E::Group: FromIterator<E>,
        {
            if self.expr.is_atom() {
                self.expr = E::from_atom(mem::replace(
                    &mut self.var,
                    mem::replace(&mut self.expr, E::empty()).unwrap_atom(),
                ));
                true
            } else {
                false
            }
        }

        /// Generates a unit substitution from a substitution term.
        #[inline]
        pub fn unit<U>(self) -> U
        where
            U: FromIterator<Self>,
        {
            Some(self).into_iter().collect()
        }

        #[inline]
        fn iter(self) -> impl Iterator<Item = E> {
            util::two_item_iter(E::from_atom(self.var), self.expr)
        }
    }

    impl<E> Clone for Term<E>
    where
        E: Expression,
        E::Atom: Clone,
        E::Group: FromIterator<E>,
    {
        #[inline]
        fn clone(&self) -> Self {
            Self::new(self.var.clone(), self.expr.clone())
        }
    }

    impl<E> Copy for Term<E>
    where
        E: Copy + Expression,
        E::Atom: Copy,
        E::Group: FromIterator<E>,
    {
    }

    impl<E> PartialEq for Term<E>
    where
        E: Expression,
        E::Atom: PartialEq,
    {
        #[inline]
        fn eq(&self, other: &Self) -> bool {
            self.as_ref().eq(&other.as_ref())
        }
    }

    impl<E> Eq for Term<E>
    where
        E: Expression,
        E::Atom: PartialEq,
    {
    }

    impl<E> TryFrom<(E, E)> for Term<E>
    where
        E: Expression,
    {
        type Error = ();

        #[inline]
        fn try_from(pair: (E, E)) -> Result<Self, Self::Error> {
            Ok(Self::new(pair.0.atom().ok_or(())?, pair.1))
        }
    }

    /// Substitution Trait
    pub trait Substitution<E, V = Vec<Term<E>>>: super::Structure<E, Structure<E, V>>
    where
        E: Expression,
        E::Group: Container<E>,
        V: Container<Term<E>>,
    {
        /// Iterator over elements by reference.
        type Iter<'s>: Iterator<Item = TermRef<'s, E>>
        where
            E: 's;

        /// Returns an iterator over the elements by reference.
        fn iter(&self) -> Self::Iter<'_>;

        /// Returns an iterator over the variables by reference.
        #[inline]
        fn vars(&self) -> VarsIter<E, Self::Iter<'_>> {
            VarsIter(self.iter())
        }

        /// Returns an iterator over the expressions by reference.
        #[inline]
        fn exprs(&self) -> ExprsIter<E, Self::Iter<'_>> {
            ExprsIter(self.iter())
        }

        /// Builds an empty `Substitution`.
        #[inline]
        fn empty() -> Self
        where
            Self: Sized,
        {
            Self::from(Structure::from_iter(None))
        }

        /// Checks if the `Substitution` is empty.
        #[inline]
        fn is_empty(&self) -> bool {
            self.iter().next().is_none()
        }

        /// Builds an identity `Substitution` over the iterator of atoms.
        #[inline]
        fn identity<I>(atoms: I) -> Self
        where
            Self: Sized,
            E::Atom: Clone,
            I: IntoIterator<Item = E::Atom>,
        {
            Self::from(atoms.into_iter().map(Term::identity).collect())
        }

        /// Checks if all of the elements of `&self` are the identity substitution.
        #[inline]
        fn is_identity(&self) -> bool
        where
            E::Atom: PartialEq,
        {
            self.iter().all(move |t| t.is_identity())
        }

        /// Builds a unit `Substitution`.
        #[inline]
        fn unit(var: E::Atom, expr: E) -> Self
        where
            Self: Sized,
        {
            Self::from(Term::new(var, expr).unit())
        }

        /// Returns corresponding expression which `var` completes to under substitution.
        #[inline]
        fn get(&self, var: &E::Atom) -> Option<&E>
        where
            E::Atom: PartialEq,
        {
            self.iter().find(move |t| t.var == var).map(move |t| t.expr)
        }

        /// Returns corresponding expression which `var` completes to under substitution.
        #[inline]
        fn get_owned(&self, var: &E::Atom) -> Option<E>
        where
            E::Atom: Clone + PartialEq,
            E::Group: FromIterator<E>,
        {
            self.get(var).map(E::clone)
        }

        /// Performs substitution on an atomic expression.
        #[inline]
        fn apply_atom(&self, atom: E::Atom) -> E
        where
            E::Atom: Clone + PartialEq,
            E::Group: FromIterator<E>,
        {
            self.get_owned(&atom)
                .unwrap_or_else(move || E::from_atom(atom))
        }

        /// Performs substitution on an atomic expression by reference.
        #[inline]
        fn apply_atom_ref(&self, atom: &E::Atom) -> E
        where
            E::Atom: Clone + PartialEq,
            E::Group: FromIterator<E>,
        {
            self.get_owned(atom)
                .unwrap_or_else(move || E::from_atom(atom.clone()))
        }

        /// Performs substitution on a grouped expression.
        fn apply_group(&self, group: E::Group) -> E::Group
        where
            E::Atom: Clone + PartialEq,
            E::Group: FromIterator<E>,
        {
            group.substitute(move |atom| self.apply_atom(atom))
        }

        /// Performs substitution on a grouped expression by reference.
        fn apply_group_ref(&self, group: &GroupRef<E>) -> E::Group
        where
            E::Atom: Clone + PartialEq,
            E::Group: FromIterator<E>,
        {
            group.substitute_ref(move |atom| self.apply_atom_ref(atom))
        }

        /// Performs substitution on an expression.
        #[inline]
        fn apply(&self, expr: E) -> E
        where
            E::Atom: Clone + PartialEq,
            E::Group: Container<E>,
        {
            expr.substitute(move |atom| self.apply_atom(atom))
        }

        /// Performs substitution on an expression by reference.
        #[inline]
        fn apply_ref(&self, expr: &E) -> E
        where
            E::Atom: Clone + PartialEq,
            E::Group: Container<E>,
        {
            expr.substitute_ref(move |atom| self.apply_atom_ref(atom))
        }

        /// Extends the given substitution by one variable-expression pair.
        #[inline]
        fn push(&mut self, var: E::Atom, expr: E) -> &mut Self
        where
            Self: Sized,
        {
            self.push_term(Term::new(var, expr))
        }

        /// Extends the given substitution by the one term.
        #[inline]
        fn push_term(&mut self, term: Term<E>) -> &mut Self
        where
            Self: Sized,
        {
            *self = Self::from(
                mem::replace(self, Self::empty())
                    .structure()
                    .push_inner(term),
            );
            self
        }

        /// Deduplicates the substitution.
        #[inline]
        fn dedup(&mut self) -> &mut Self
        where
            Self: Sized,
            E::Atom: PartialEq,
        {
            *self = Self::from(mem::replace(self, Self::empty()).structure().dedup_inner());
            self
        }

        /// Sorts the substitution by variable.
        #[inline]
        fn sort(&mut self) -> &mut Self
        where
            Self: Sized,
            E::Atom: Ord,
        {
            *self = Self::from(mem::replace(self, Self::empty()).structure().sort_inner());
            self
        }

        /// Reduces the substitution to its canonical form.
        #[inline]
        fn canonicalize(&mut self) -> &mut Self
        where
            Self: Sized,
            E::Atom: Ord,
        {
            *self = Self::from(
                mem::replace(self, Self::empty())
                    .structure()
                    .canonicalize_inner(),
            );
            self
        }

        /// Tries to generate a substitution from two expressions.
        // FIXME: find a way to accept `&E` or `ExprRef<E>`
        #[inline]
        fn generate<F>(lhs: &E, rhs: &E, can_substitute: F) -> Option<Directed<Self>>
        where
            Self: Sized,
            E::Atom: Clone + PartialEq,
            F: FnMut(&E::Atom) -> bool,
        {
            generate::<_, Structure<_, V>, _>(lhs, rhs, can_substitute)
                .map(move |d| d.map(Self::from))
        }
    }

    /// Iterator over Substitution Variables
    #[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
    pub struct VarsIter<'s, E, I>(I)
    where
        E: 's + Expression,
        I: Iterator<Item = TermRef<'s, E>>;

    impl<'s, E, I> Iterator for VarsIter<'s, E, I>
    where
        E: 's + Expression,
        I: Iterator<Item = TermRef<'s, E>>,
    {
        type Item = &'s E::Atom;

        #[inline]
        fn next(&mut self) -> Option<Self::Item> {
            self.0.next().map(move |t| t.var)
        }

        #[inline]
        fn size_hint(&self) -> (usize, Option<usize>) {
            self.0.size_hint()
        }
    }

    /// Iterator over Substitution Expressions
    #[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
    pub struct ExprsIter<'s, E, I>(I)
    where
        E: 's + Expression,
        I: Iterator<Item = TermRef<'s, E>>;

    impl<'s, E, I> Iterator for ExprsIter<'s, E, I>
    where
        E: 's + Expression,
        I: Iterator<Item = TermRef<'s, E>>,
    {
        type Item = &'s E;

        #[inline]
        fn next(&mut self) -> Option<Self::Item> {
            self.0.next().map(move |t| t.expr)
        }

        #[inline]
        fn size_hint(&self) -> (usize, Option<usize>) {
            self.0.size_hint()
        }
    }

    /// Substitution Structure Type
    #[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
    pub struct Structure<E, V = Vec<Term<E>>>
    where
        E: Expression,
        V: Container<Term<E>>,
    {
        /// Substitution terms
        pub terms: V,

        /// Phantom Marker
        __: PhantomData<E>,
    }

    impl<E, V> Structure<E, V>
    where
        E: Expression,
        V: Container<Term<E>>,
    {
        /// Builds a new [`Structure`] from a [`Term`] container.
        #[inline]
        pub fn new(terms: V) -> Self {
            Self {
                terms,
                __: PhantomData,
            }
        }

        #[inline]
        fn push_inner(self, term: Term<E>) -> Self {
            self.into_iter().chain(Some(term)).collect()
        }

        #[inline]
        fn dedup_inner(self) -> Self
        where
            E::Atom: PartialEq,
        {
            let mut terms = self.into_iter().collect::<Vec<_>>();
            terms.dedup_by(move |l, r| l.var.eq(&r.var));
            Self::from_iter(terms)
        }

        #[inline]
        fn sort_inner(self) -> Self
        where
            E::Atom: Ord,
        {
            let mut terms = self.into_iter().collect::<Vec<_>>();
            terms.sort_by(move |l, r| l.var.cmp(&r.var));
            Self::from_iter(terms)
        }

        #[inline]
        fn canonicalize_inner(self) -> Self
        where
            E::Atom: Ord,
        {
            self.sort_inner()
                .dedup_inner()
                .into_iter()
                .filter(move |t| !t.is_identity())
                .collect()
        }
    }

    impl<E, V> Default for Structure<E, V>
    where
        E: Expression,
        V: Container<Term<E>>,
    {
        #[inline]
        fn default() -> Self {
            Self::new(V::from_iter(None))
        }
    }

    impl<E, V> IntoIterator for Structure<E, V>
    where
        E: Expression,
        V: Container<Term<E>>,
    {
        type Item = Term<E>;

        type IntoIter = <V as IntoIterator>::IntoIter;

        #[inline]
        fn into_iter(self) -> Self::IntoIter {
            self.terms.into_iter()
        }
    }

    impl<E, V> FromIterator<Term<E>> for Structure<E, V>
    where
        E: Expression,
        V: Container<Term<E>>,
    {
        #[inline]
        fn from_iter<I>(iter: I) -> Self
        where
            I: IntoIterator<Item = Term<E>>,
        {
            Self::new(V::from_iter(iter))
        }
    }

    impl<E, V> From<Structure<E, V>> for Expr<E>
    where
        E: Expression,
        E::Group: FromIterator<E>,
        V: Container<Term<E>>,
    {
        #[inline]
        fn from(structure: Structure<E, V>) -> Self {
            Self::Group(structure.into_iter().map(Term::iter).flatten().collect())
        }
    }

    /// Substitution Shape Error Type
    #[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
    pub enum ShapeError {
        /// The expression is not a group.
        NotGroup,

        /// The expression is not grouped in pairs.
        NotGroupedInPairs,

        /// The expression does not have the right group shape.
        BadGroupShape(usize),
    }

    /// Checks if an atom matches the `Substitution` pattern.
    #[inline]
    pub fn matches_atom<E>(atom: &E::Atom) -> Result<(), ShapeError>
    where
        E: Expression,
    {
        let _ = atom;
        Err(ShapeError::NotGroup)
    }

    /// Checks if a group matches the `Substitution` pattern.
    #[inline]
    pub fn matches_group<E>(group: &GroupRef<E>) -> Result<(), ShapeError>
    where
        E: Expression,
    {
        for (i, pair) in util::by_pairs(group.iter()).enumerate() {
            match pair {
                Some((var, _)) => {
                    if !var.is_atom() {
                        return Err(ShapeError::BadGroupShape(i));
                    }
                }
                _ => return Err(ShapeError::NotGroupedInPairs),
            }
        }
        Ok(())
    }

    /// Checks if an expression matches the `Substitution` pattern.
    #[inline]
    pub fn matches<E>(expr: &ExprRef<E>) -> Result<(), ShapeError>
    where
        E: Expression,
    {
        match expr {
            ExprRef::Atom(atom) => matches_atom::<E>(atom),
            ExprRef::Group(group) => matches_group::<E>(group),
        }
    }

    impl<E, V> Matcher<E> for Structure<E, V>
    where
        E: Expression,
        V: Container<Term<E>>,
    {
        type Error = ShapeError;

        #[inline]
        fn matches_atom(atom: &E::Atom) -> Result<(), Self::Error> {
            matches_atom::<E>(atom)
        }

        #[inline]
        fn matches_group(group: GroupRef<E>) -> Result<(), Self::Error> {
            matches_group::<E>(&group)
        }
    }

    impl<E, V> TryFrom<Expr<E>> for Structure<E, V>
    where
        E: Expression,
        E::Group: IntoIterator<Item = E>,
        V: Container<Term<E>>,
    {
        type Error = <Structure<E, V> as Matcher<E>>::Error;

        #[inline]
        fn try_from(expr: Expr<E>) -> Result<Self, Self::Error> {
            util::by_pairs(expr.group().ok_or(Self::Error::NotGroup)?)
                .enumerate()
                .map(move |(i, pair)| match pair {
                    Some(pair) => pair
                        .try_into()
                        .map_err(move |_| Self::Error::BadGroupShape(i)),
                    _ => Err(Self::Error::NotGroupedInPairs),
                })
                .collect()
        }
    }

    impl<E, V> Shape<E> for Structure<E, V>
    where
        E: Expression,
        E::Group: Container<E>,
        V: Container<Term<E>>,
    {
    }

    /// Structure Vector Reference Iterator
    #[derive(Clone)]
    pub struct StructureVecIter<'s, E>(slice::Iter<'s, Term<E>>)
    where
        E: Expression;

    impl<E> AsRef<[Term<E>]> for StructureVecIter<'_, E>
    where
        E: Expression,
    {
        #[inline]
        fn as_ref(&self) -> &[Term<E>] {
            self.0.as_ref()
        }
    }

    impl<'s, E> DoubleEndedIterator for StructureVecIter<'s, E>
    where
        E: Expression,
    {
        #[inline]
        fn next_back(&mut self) -> Option<TermRef<'s, E>> {
            self.0.next_back().map(Term::as_ref)
        }
    }

    impl<E> ExactSizeIterator for StructureVecIter<'_, E> where E: Expression {}

    impl<E> iter::FusedIterator for StructureVecIter<'_, E> where E: Expression {}

    impl<'s, E> Iterator for StructureVecIter<'s, E>
    where
        E: Expression,
    {
        type Item = TermRef<'s, E>;

        #[inline]
        fn next(&mut self) -> Option<Self::Item> {
            self.0.next().map(Term::as_ref)
        }

        #[inline]
        fn size_hint(&self) -> (usize, Option<usize>) {
            self.0.size_hint()
        }

        #[inline]
        fn count(self) -> usize {
            self.0.count()
        }
    }

    impl<E> Substitution<E> for Structure<E>
    where
        E: Expression,
        E::Group: Container<E>,
    {
        type Iter<'s>
        where
            E: 's,
        = StructureVecIter<'s, E>;

        #[inline]
        fn iter(&self) -> Self::Iter<'_> {
            StructureVecIter(self.terms.iter())
        }

        #[inline]
        fn push_term(&mut self, term: Term<E>) -> &mut Self {
            *self = mem::take(self).push_inner(term);
            self
        }

        #[inline]
        fn dedup(&mut self) -> &mut Self
        where
            E::Atom: PartialEq,
        {
            *self = mem::take(self).dedup_inner();
            self
        }

        #[inline]
        fn sort(&mut self) -> &mut Self
        where
            E::Atom: Ord,
        {
            *self = mem::take(self).sort_inner();
            self
        }

        #[inline]
        fn canonicalize(&mut self) -> &mut Self
        where
            E::Atom: Ord,
        {
            *self = mem::take(self).canonicalize_inner();
            self
        }
    }

    /// Directed Substitution
    pub enum Directed<S> {
        /// Forward Substitution
        Forward(S),

        /// Backward Substitution
        Backward(S),
    }

    /// Forward Substitution Boolean
    pub type IsForward = bool;

    impl<S> Directed<S> {
        /// Returns `true` if the substitution is a `Forward` substitution.
        #[inline]
        pub fn is_forward(&self) -> bool {
            matches!(self, Self::Forward(_))
        }

        /// Returns `true` if the substitution is a `Backward` substitution.
        #[inline]
        pub fn is_backward(&self) -> bool {
            matches!(self, Self::Backward(_))
        }

        /// Returns `Some` with the inner substitution if `self` is `Forward`.
        #[must_use]
        #[inline]
        pub fn forward(self) -> Option<S> {
            match self {
                Self::Forward(substitution) => Some(substitution),
                _ => None,
            }
        }

        /// Returns `Some` with the inner substitution if `self` is `Forward`.
        #[must_use]
        #[inline]
        pub fn forward_ref(&self) -> Option<&S> {
            match self {
                Self::Forward(substitution) => Some(substitution),
                _ => None,
            }
        }

        /// Returns `Some` with the inner substitution if `self` is `Backward`.
        #[must_use]
        #[inline]
        pub fn backward(self) -> Option<S> {
            match self {
                Self::Backward(substitution) => Some(substitution),
                _ => None,
            }
        }

        /// Returns `Some` with the inner substitution if `self` is `Backward`.
        #[must_use]
        #[inline]
        pub fn backward_ref(&self) -> Option<&S> {
            match self {
                Self::Backward(substitution) => Some(substitution),
                _ => None,
            }
        }

        /// Maps a `Directed<S>` to `Directed<T>` by applying a function to a contained value.
        #[inline]
        pub fn map<T, F>(self, f: F) -> Directed<T>
        where
            F: FnOnce(S) -> T,
        {
            match self {
                Self::Forward(substitution) => Directed::Forward(f(substitution)),
                Self::Backward(substitution) => Directed::Backward(f(substitution)),
            }
        }

        /// Returns the inner substitution.
        #[inline]
        pub fn substitution(self) -> S {
            match self {
                Self::Forward(substitution) | Self::Backward(substitution) => substitution,
            }
        }

        /// Packs the enumeration from a `(bool, S)` pair.
        #[inline]
        pub fn pack(is_forward: IsForward, substitution: S) -> Self {
            if is_forward {
                Self::Forward(substitution)
            } else {
                Self::Backward(substitution)
            }
        }

        /// Unpacks the enumeration into a `(bool, S)` pair.
        #[inline]
        pub fn unpack(self) -> (IsForward, S) {
            (self.is_forward(), self.substitution())
        }
    }

    /// Tries to generate a substitution from two atomic expressions.
    #[inline]
    pub fn generate_from_atoms<E, S, F>(
        lhs: &E::Atom,
        rhs: &E::Atom,
        mut can_substitute: F,
    ) -> Option<Directed<S>>
    where
        E: Expression,
        E::Atom: Clone + PartialEq,
        E::Group: FromIterator<E>,
        S: FromIterator<Term<E>> + IntoIterator<Item = Term<E>>,
        F: FnMut(&E::Atom) -> bool,
    {
        generate_from_atoms_inner(lhs, rhs, &mut can_substitute)
    }

    /// Tries to generate a substitution from two grouped expressions.
    // FIXME: find a way to accept `&E::Group` or `GroupRef<E>`
    #[inline]
    pub fn generate_from_groups<E, S, F>(
        lhs: &GroupRef<E>,
        rhs: &GroupRef<E>,
        mut can_substitute: F,
    ) -> Option<Directed<S>>
    where
        E: Expression,
        E::Atom: Clone + PartialEq,
        E::Group: FromIterator<E>,
        S: FromIterator<Term<E>> + IntoIterator<Item = Term<E>>,
        F: FnMut(&E::Atom) -> bool,
    {
        generate_from_groups_inner(lhs, rhs, &mut can_substitute)
    }

    /// Tries to generate a substitution from two expressions.
    // FIXME: find a way to accept `&E` or `ExprRef<E>`
    #[inline]
    pub fn generate<E, S, F>(lhs: &E, rhs: &E, mut can_substitute: F) -> Option<Directed<S>>
    where
        E: Expression,
        E::Atom: Clone + PartialEq,
        E::Group: FromIterator<E>,
        S: FromIterator<Term<E>> + IntoIterator<Item = Term<E>>,
        F: FnMut(&E::Atom) -> bool,
    {
        generate_inner(lhs.cases(), rhs.cases(), &mut can_substitute)
    }

    fn generate_from_atoms_inner<E, S, F>(
        lhs: &E::Atom,
        rhs: &E::Atom,
        can_substitute: &mut F,
    ) -> Option<Directed<S>>
    where
        E: Expression,
        E::Atom: Clone + PartialEq,
        E::Group: FromIterator<E>,
        S: FromIterator<Term<E>> + IntoIterator<Item = Term<E>>,
        F: FnMut(&E::Atom) -> bool,
    {
        if lhs == rhs {
            Some(Directed::Forward(S::from_iter(None)))
        } else if can_substitute(lhs) {
            Some(Directed::Forward(
                Term::new(lhs.clone(), E::from_atom(rhs.clone())).unit(),
            ))
        } else if can_substitute(rhs) {
            Some(Directed::Backward(
                Term::new(rhs.clone(), E::from_atom(lhs.clone())).unit(),
            ))
        } else {
            None
        }
    }

    fn generate_from_groups_inner<E, S, F>(
        lhs: &GroupRef<E>,
        rhs: &GroupRef<E>,
        can_substitute: &mut F,
    ) -> Option<Directed<S>>
    where
        E: Expression,
        E::Atom: Clone + PartialEq,
        E::Group: FromIterator<E>,
        S: FromIterator<Term<E>> + IntoIterator<Item = Term<E>>,
        F: FnMut(&E::Atom) -> bool,
    {
        // FIXME: use `S as FromIterator` to construct the final substitution
        // instead of relying on an intermediate `Vec`
        let mut is_flipped = false;
        let mut substitution = Vec::<Term<_>>::new();
        let mut lhs_iter = lhs.iter();
        let mut rhs_iter = rhs.iter();
        for (lhs, rhs) in lhs_iter.by_ref().zip(rhs_iter.by_ref()) {
            match generate_inner::<_, S, _>(lhs.cases(), rhs.cases(), can_substitute) {
                Some(generated) => {
                    let (is_forward, generated) = generated.unpack();
                    if !is_forward {
                        if is_flipped
                            || !substitution
                                .iter_mut()
                                .all(|t| t.flip_in_place() && can_substitute(&t.var))
                        {
                            return None;
                        }
                        is_flipped = true;
                        substitution.extend(generated);
                    } else if is_flipped {
                        for term in generated {
                            let flipped = term.flip()?;
                            if !can_substitute(&flipped.var) {
                                return None;
                            }
                            substitution.push(flipped);
                        }
                    } else {
                        substitution.extend(generated);
                    }
                }
                _ => return None,
            }
        }
        if lhs_iter.next().is_some() || rhs_iter.next().is_some() {
            None
        } else {
            // FIXME: we can probably safely remove the `is_identity` checks
            Some(Directed::pack(
                !is_flipped,
                substitution
                    .into_iter()
                    .filter(move |s| !s.is_identity())
                    .collect(),
            ))
        }
    }

    fn generate_inner<E, S, F>(
        lhs: ExprRef<'_, E>,
        rhs: ExprRef<'_, E>,
        can_substitute: &mut F,
    ) -> Option<Directed<S>>
    where
        E: Expression,
        E::Atom: Clone + PartialEq,
        E::Group: FromIterator<E>,
        S: FromIterator<Term<E>> + IntoIterator<Item = Term<E>>,
        F: FnMut(&E::Atom) -> bool,
    {
        match (&lhs, &rhs) {
            (ExprRef::Atom(lhs_atom), ExprRef::Atom(rhs_atom)) => {
                generate_from_atoms(*lhs_atom, *rhs_atom, can_substitute)
            }
            (ExprRef::Atom(lhs), _) if can_substitute(lhs) => Some(Directed::Forward(
                Term::new((*lhs).clone(), rhs.to_owned()).unit(),
            )),
            (_, ExprRef::Atom(rhs)) if can_substitute(rhs) => Some(Directed::Backward(
                Term::new((*rhs).clone(), lhs.to_owned()).unit(),
            )),
            (ExprRef::Group(lhs), ExprRef::Group(rhs)) => {
                generate_from_groups_inner(lhs, rhs, can_substitute)
            }
            _ => None,
        }
    }

    /// Generalizes a set of expressions to a single expression and substitutions.
    #[inline]
    pub fn generalize<E, F, G, S, C>(
        exprs: &[E],
        mut can_substitute: F,
        mut atom_generator: G,
    ) -> (E, C)
    where
        E: Expression,
        E::Atom: Clone + PartialEq,
        E::Group: FromIterator<E> + IntoIterator<Item = E>,
        F: FnMut(&E::Atom) -> bool,
        G: FnMut() -> E::Atom,
        S: Substitution<E>,
        C: FromIterator<S>,
    {
        generalize_inner(exprs, &mut can_substitute, &mut atom_generator)
    }

    #[inline]
    fn generalize_to_atom<E, S, C>(target: &E::Atom, exprs: &[E]) -> C
    where
        E: Expression,
        E::Atom: Clone + PartialEq,
        E::Group: FromIterator<E> + IntoIterator<Item = E>,
        S: Substitution<E>,
        C: FromIterator<S>,
    {
        exprs
            .iter()
            .map(move |expr| match expr.atom_ref() {
                Some(atom) if target == atom => S::empty(),
                _ => S::unit(target.clone(), (*expr).to_owned()),
            })
            .collect()
    }

    fn transpose_substitutions<E, S>(
        expr_count: usize,
        mut substitutions: Vec<Vec<S>>,
    ) -> impl Iterator<Item = S>
    where
        E: Expression,
        E::Atom: PartialEq,
        E::Group: FromIterator<E> + IntoIterator<Item = E>,
        S: Substitution<E>,
    {
        let mut result = Vec::with_capacity(expr_count);
        for _ in 0..expr_count {
            result.push(S::from(
                substitutions
                    .iter_mut()
                    .map(move |s| {
                        let mut s = s.pop().unwrap().structure();
                        s.dedup(); // FIXME: is this correct?
                        s
                    })
                    .flatten()
                    .collect(),
            ));
        }
        result.into_iter().rev()
    }

    fn generalize_inner<E, F, G, S, C>(
        exprs: &[E],
        can_substitute: &mut F,
        atom_generator: &mut G,
    ) -> (E, C)
    where
        E: Expression,
        E::Atom: Clone + PartialEq,
        E::Group: FromIterator<E> + IntoIterator<Item = E>,
        F: FnMut(&E::Atom) -> bool,
        G: FnMut() -> E::Atom,
        S: Substitution<E>,
        C: FromIterator<S>,
    {
        match exprs.len() {
            0 => (E::empty(), C::from_iter(None)),
            1 => (exprs[0].to_owned(), C::from_iter(Some(S::empty()))),
            expr_count => {
                match exprs.iter().find_map(move |e| e.atom()) {
                    Some(atom) if can_substitute(atom) => {
                        return (E::from_atom(atom.clone()), generalize_to_atom(atom, exprs));
                    }
                    None => {
                        if let Some(group_size) = (&exprs[0]).unwrap_group().len() {
                            let groups = exprs.iter().map(move |e| e.unwrap_group());
                            if groups.clone().all(move |g| g.len() == Some(group_size)) {
                                let (expr_base, inner_substitutions) = (0..group_size)
                                    .into_iter()
                                    .map(move |i| {
                                        // FIXME: remove the call to `.to_owned` if possible
                                        generalize_inner::<_, _, _, _, Vec<S>>(
                                            &groups
                                                .clone()
                                                .map(move |g| g.get(i).unwrap().to_owned())
                                                .collect::<Vec<_>>(),
                                            can_substitute,
                                            atom_generator,
                                        )
                                    })
                                    .unzip::<_, _, Vec<_>, Vec<_>>();
                                return (
                                    E::from_group(expr_base.into_iter().collect()),
                                    transpose_substitutions(expr_count, inner_substitutions)
                                        .collect(),
                                );
                            }
                        }
                    }
                    _ => {}
                }
                let target = atom_generator();
                let substitutions = generalize_to_atom(&target, exprs);
                (E::from_atom(target), substitutions)
            }
        }
    }
}

/// Composition Module
#[cfg(feature = "composition")]
#[cfg_attr(docsrs, doc(cfg(feature = "composition")))]
pub mod composition {
    use {
        super::*,
        alloc::vec::Vec,
        core::{iter, slice},
    };

    /// Evaluation Shape
    #[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
    pub enum EvaluationShape<R, C> {
        /// Rule Shape
        Rule(R),

        /// Composition Shape
        Composition(C),
    }

    /// Stored Rule Reference
    #[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
    pub enum StoredRuleRef<'e, R, K> {
        /// Rule
        Rule(&'e R),

        /// Key
        Key(&'e K),
    }

    impl<'e, R, K> StoredRuleRef<'e, R, K> {
        /// Returns an owned [`StoredRule`] value.
        #[inline]
        pub fn to_owned(&self) -> StoredRule<R, K>
        where
            R: Clone,
            K: Clone,
        {
            match self {
                Self::Rule(rule) => StoredRule::Rule(Clone::clone(rule)),
                Self::Key(key) => StoredRule::Key(Clone::clone(key)),
            }
        }
    }

    impl<'e, R, K> From<&'e StoredRule<R, K>> for StoredRuleRef<'e, R, K> {
        #[inline]
        fn from(stored: &'e StoredRule<R, K>) -> Self {
            stored.as_ref()
        }
    }

    /// Stored Rule
    #[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
    pub enum StoredRule<R, K> {
        /// Rule
        Rule(R),

        /// Key
        Key(K),
    }

    impl<R, K> StoredRule<R, K> {
        /// Returns the [`&StoredRule`](StoredRule) as a [`StoredRuleRef`].
        #[inline]
        pub fn as_ref(&self) -> StoredRuleRef<'_, R, K> {
            match self {
                Self::Rule(rule) => StoredRuleRef::Rule(rule),
                Self::Key(key) => StoredRuleRef::Key(key),
            }
        }
    }

    impl<E, R, K> From<StoredRule<R, K>> for Expr<E>
    where
        E: Expression,
        E::Group: Container<E>,
        R: Rule<E>,
        K: Into<E::Atom>,
    {
        #[inline]
        fn from(rule: StoredRule<R, K>) -> Self {
            match rule {
                StoredRule::Rule(rule) => rule.into().into(),
                StoredRule::Key(key) => Self::Atom(key.into()),
            }
        }
    }

    impl<E, R, K> TryFrom<Expr<E>> for StoredRule<R, K>
    where
        E: Expression,
        E::Group: Container<E>,
        R: Rule<E>,
        K: TryFrom<E::Atom>,
    {
        type Error = ();

        #[inline]
        fn try_from(expr: Expr<E>) -> Result<Self, Self::Error> {
            if expr.is_atom() {
                match expr.unwrap_atom().try_into() {
                    Ok(key) => Ok(Self::Key(key)),
                    _ => Err(()),
                }
            } else {
                match R::try_from(E::from_expr(expr)) {
                    Ok(rule) => Ok(Self::Rule(rule)),
                    _ => Err(()),
                }
            }
        }
    }

    /// Composition Term Reference Type
    #[derive(Debug, Eq, PartialEq)]
    pub struct TermRef<'e, R, S, K> {
        /// [`StoredRule`] Reference
        pub rule: StoredRuleRef<'e, R, K>,

        /// [`Substitution`] Reference
        pub subst: &'e S,
    }

    impl<'e, R, S, K> TermRef<'e, R, S, K> {
        /// Builds a new composition term reference.
        #[inline]
        pub fn new(rule: StoredRuleRef<'e, R, K>, subst: &'e S) -> Self {
            Self { rule, subst }
        }

        /// Returns an owned [`Term`].
        #[inline]
        pub fn to_owned(&self) -> Term<R, S, K>
        where
            R: Clone,
            S: Clone,
            K: Clone,
        {
            Term::new(self.rule.to_owned(), self.subst.clone())
        }
    }

    impl<'e, R, S, K> From<&'e Term<R, S, K>> for TermRef<'e, R, S, K> {
        #[inline]
        fn from(term: &'e Term<R, S, K>) -> Self {
            term.as_ref()
        }
    }

    /// Composition Term Type
    #[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
    pub struct Term<R, S, K> {
        /// [`StoredRule`] Object
        pub rule: StoredRule<R, K>,

        /// [`Substitution`] Object
        pub subst: S,
    }

    impl<R, S, K> Term<R, S, K> {
        /// Builds a new composition term.
        #[inline]
        pub fn new(rule: StoredRule<R, K>, subst: S) -> Self {
            Self { rule, subst }
        }

        /// Returns the [`&Term`](Term) as a [`TermRef`].
        #[inline]
        pub fn as_ref(&self) -> TermRef<'_, R, S, K> {
            TermRef::new(self.rule.as_ref(), &self.subst)
        }

        #[inline]
        fn iter<E>(self) -> impl Iterator<Item = E>
        where
            E: Expression,
            E::Group: Container<E>,
            R: Rule<E>,
            S: Substitution<E>,
            K: Into<E::Atom>,
        {
            util::two_item_iter(E::from_expr(Into::into(self.rule)), self.subst.into())
        }
    }

    impl<E, R, S, K> TryFrom<(E, E)> for Term<R, S, K> {
        type Error = ();

        #[inline]
        fn try_from((rule, subst): (E, E)) -> Result<Self, Self::Error> {
            // TODO: Ok(Self::new(eval.try_into()?, subst.try_into()?))
            let _ = (rule, subst);
            todo!()
        }
    }

    /// Composition Trait
    pub trait Composition<E, R, S, K = <E as Expression>::Atom, V = Vec<Term<R, S, K>>>:
        super::Structure<E, Structure<E, R, S, K, V>>
    where
        E: Expression,
        E::Group: Container<E>,
        R: Rule<E>,
        S: Substitution<E>,
        K: Into<E::Atom>,
        V: Container<Term<R, S, K>>,
    {
        /// Iterator over elements by reference.
        type Iter<'e>: Iterator<Item = TermRef<'e, R, S, K>>
        where
            R: 'e,
            S: 'e,
            K: 'e;

        /// Returns an iterator over the elements by reference.
        fn iter(&self) -> Self::Iter<'_>;

        /// Builds an empty `Composition`.
        #[inline]
        fn empty() -> Self
        where
            Self: Sized,
        {
            Self::from(Structure::from_iter(None))
        }

        /// Checks if the `Composition` is empty.
        #[inline]
        fn is_empty(&self) -> bool {
            self.iter().next().is_none()
        }

        /// Evaluates the composition.
        #[inline]
        fn flat_resolve<F>(self, resolver: F) -> Result<R, E::Atom>
        where
            Self: Sized,
            F: FnMut(&K) -> Option<R>,
        {
            let _ = resolver;
            todo!()
        }

        /// Evaluates the composition.
        #[inline]
        fn resolve<F>(self, resolver: F) -> Result<R, E::Atom>
        where
            Self: Sized,
            F: FnMut(&K) -> Option<EvaluationShape<R, Self>>,
        {
            let _ = resolver;
            todo!()
        }
    }

    /// Composition Structure Type
    #[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
    pub struct Structure<E, R, S, K = <E as Expression>::Atom, V = Vec<Term<R, S, K>>>
    where
        E: Expression,
        E::Group: Container<E>,
        R: Rule<E>,
        S: Substitution<E>,
        V: Container<Term<R, S, K>>,
    {
        /// Composition terms
        pub terms: V,

        /// Phantom Marker
        __: PhantomData<(E, R, S, K)>,
    }

    impl<E, R, S, K, V> Structure<E, R, S, K, V>
    where
        E: Expression,
        E::Group: Container<E>,
        R: Rule<E>,
        S: Substitution<E>,
        V: Container<Term<R, S, K>>,
    {
        /// Builds a new [`Structure`] from a [`Term`] container.
        #[inline]
        pub fn new(terms: V) -> Self {
            Self {
                terms,
                __: PhantomData,
            }
        }
    }

    impl<E, R, S, K, V> Default for Structure<E, R, S, K, V>
    where
        E: Expression,
        E::Group: Container<E>,
        R: Rule<E>,
        S: Substitution<E>,
        V: Container<Term<R, S, K>>,
    {
        #[inline]
        fn default() -> Self {
            Self::new(V::from_iter(None))
        }
    }

    impl<E, R, S, K, V> IntoIterator for Structure<E, R, S, K, V>
    where
        E: Expression,
        E::Group: Container<E>,
        R: Rule<E>,
        S: Substitution<E>,
        V: Container<Term<R, S, K>>,
    {
        type Item = Term<R, S, K>;

        type IntoIter = <V as IntoIterator>::IntoIter;

        #[inline]
        fn into_iter(self) -> Self::IntoIter {
            self.terms.into_iter()
        }
    }

    impl<E, R, S, K, V> FromIterator<Term<R, S, K>> for Structure<E, R, S, K, V>
    where
        E: Expression,
        E::Group: Container<E>,
        R: Rule<E>,
        S: Substitution<E>,
        V: Container<Term<R, S, K>>,
    {
        #[inline]
        fn from_iter<I>(iter: I) -> Self
        where
            I: IntoIterator<Item = Term<R, S, K>>,
        {
            Self::new(V::from_iter(iter))
        }
    }

    impl<E, R, S, K, V> From<Structure<E, R, S, K, V>> for Expr<E>
    where
        E: Expression,
        E::Group: Container<E>,
        R: Rule<E>,
        S: Substitution<E>,
        K: Into<E::Atom>,
        V: Container<Term<R, S, K>>,
    {
        #[inline]
        fn from(structure: Structure<E, R, S, K, V>) -> Self {
            Self::Group(structure.into_iter().map(Term::iter).flatten().collect())
        }
    }

    /// Composition Shape Error Type
    #[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
    pub enum ShapeError {}

    /// Checks if an atom matches the `Composition` pattern.
    #[inline]
    pub fn matches_atom<E>(atom: &E::Atom) -> Result<(), ShapeError>
    where
        E: Expression,
    {
        // FIXME: implement
        let _ = atom;
        todo!()
    }

    /// Checks if a group matches the `Composition` pattern.
    #[inline]
    pub fn matches_group<E>(group: &GroupRef<E>) -> Result<(), ShapeError>
    where
        E: Expression,
    {
        // FIXME: implement
        let _ = group;
        todo!()
    }

    /// Checks if an expression matches the `Composition` pattern.
    #[inline]
    pub fn matches<E>(expr: &ExprRef<E>) -> Result<(), ShapeError>
    where
        E: Expression,
    {
        match expr {
            ExprRef::Atom(atom) => matches_atom::<E>(atom),
            ExprRef::Group(group) => matches_group::<E>(group),
        }
    }

    impl<E, R, S, K, V> Matcher<E> for Structure<E, R, S, K, V>
    where
        E: Expression,
        E::Group: Container<E>,
        R: Rule<E>,
        S: Substitution<E>,
        V: Container<Term<R, S, K>>,
    {
        type Error = ShapeError;

        #[inline]
        fn matches_atom(atom: &E::Atom) -> Result<(), Self::Error> {
            matches_atom::<E>(atom)
        }

        #[inline]
        fn matches_group(group: GroupRef<E>) -> Result<(), Self::Error> {
            matches_group::<E>(&group)
        }
    }

    impl<E, R, S, K, V> TryFrom<Expr<E>> for Structure<E, R, S, K, V>
    where
        E: Expression,
        E::Group: Container<E>,
        R: Rule<E>,
        S: Substitution<E>,
        V: Container<Term<R, S, K>>,
    {
        type Error = <Structure<E, R, S, K, V> as Matcher<E>>::Error;

        #[inline]
        fn try_from(expr: Expr<E>) -> Result<Self, Self::Error> {
            // FIXME: implement
            let _ = expr;
            todo!()
        }
    }

    impl<E, R, S, K, V> Shape<E> for Structure<E, R, S, K, V>
    where
        E: Expression,
        E::Group: Container<E>,
        R: Rule<E>,
        S: Substitution<E>,
        K: Into<E::Atom>,
        V: Container<Term<R, S, K>>,
    {
    }

    /// Structure Vector Reference Iterator
    #[derive(Clone)]
    pub struct StructureVecIter<'s, R, S, K>(slice::Iter<'s, Term<R, S, K>>);

    impl<R, S, K> AsRef<[Term<R, S, K>]> for StructureVecIter<'_, R, S, K> {
        #[inline]
        fn as_ref(&self) -> &[Term<R, S, K>] {
            self.0.as_ref()
        }
    }

    impl<'s, R, S, K> DoubleEndedIterator for StructureVecIter<'s, R, S, K> {
        #[inline]
        fn next_back(&mut self) -> Option<TermRef<'s, R, S, K>> {
            self.0.next_back().map(Term::as_ref)
        }
    }

    impl<R, S, K> ExactSizeIterator for StructureVecIter<'_, R, S, K> {}

    impl<R, S, K> iter::FusedIterator for StructureVecIter<'_, R, S, K> {}

    impl<'s, R, S, K> Iterator for StructureVecIter<'s, R, S, K> {
        type Item = TermRef<'s, R, S, K>;

        #[inline]
        fn next(&mut self) -> Option<Self::Item> {
            self.0.next().map(Term::as_ref)
        }

        #[inline]
        fn size_hint(&self) -> (usize, Option<usize>) {
            self.0.size_hint()
        }

        #[inline]
        fn count(self) -> usize {
            self.0.count()
        }
    }

    impl<E, R, S, K> Composition<E, R, S, K> for Structure<E, R, S, K>
    where
        E: Expression,
        E::Group: Container<E>,
        R: Rule<E>,
        S: Substitution<E>,
        K: Into<E::Atom>,
    {
        type Iter<'e>
        where
            R: 'e,
            S: 'e,
            K: 'e,
        = StructureVecIter<'e, R, S, K>;

        #[inline]
        fn iter(&self) -> Self::Iter<'_> {
            StructureVecIter(self.terms.iter())
        }
    }
}

/// Stored Objects Module
pub mod stored {
    use super::*;

    /// Resolvable Trait
    pub trait Resolvable<K> {
        /// Resolved Part Type
        type Part;

        /// Resolved Output Type
        type Output;

        /// Key Container Type
        type UnresolvedKeys: IntoIterator<Item = K>;

        /// Resolves all keys in the given object and returns the output or the unresolved keys.
        fn resolve<F>(self, resolver: F) -> Result<Self::Output, Self::UnresolvedKeys>
        where
            F: FnMut(&K) -> Option<Self::Part>;
    }

    /// Stored Object
    #[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
    pub enum Stored<K, V> {
        /// Key
        Key(K),

        /// Value
        Value(V),
    }

    impl<K, V> Stored<K, V> {
        /// Returns the [`&Stored`](Stored) as a [`StoredRef`].
        #[inline]
        pub fn as_ref(&self) -> StoredRef<'_, K, V> {
            match self {
                Self::Key(key) => StoredRef::Key(key),
                Self::Value(value) => StoredRef::Value(value),
            }
        }
    }

    impl<K, V> Resolvable<K> for Stored<K, V> {
        type Part = V;

        type Output = V;

        type UnresolvedKeys = Result<K, Infallible>;

        #[inline]
        fn resolve<F>(self, mut resolver: F) -> Result<Self::Output, Self::UnresolvedKeys>
        where
            F: FnMut(&K) -> Option<Self::Part>,
        {
            match self {
                Self::Key(key) => resolver(&key).ok_or(Ok(key)),
                Self::Value(value) => Ok(value),
            }
        }
    }

    /// Stored Reference
    pub type StoredRef<'r, K, V> = Stored<&'r K, &'r V>;

    impl<'r, K, V> StoredRef<'r, K, V> {
        /// Returns an owned [`Stored`] value.
        #[inline]
        pub fn to_owned(&self) -> Stored<K, V>
        where
            K: Clone,
            V: Clone,
        {
            match self {
                Self::Key(key) => Stored::Key(Clone::clone(key)),
                Self::Value(value) => Stored::Value(Clone::clone(value)),
            }
        }
    }

    impl<'r, K, V> From<&'r Stored<K, V>> for StoredRef<'r, K, V> {
        #[inline]
        fn from(stored: &'r Stored<K, V>) -> Self {
            stored.as_ref()
        }
    }

    /// Stored Shape Type
    #[derive(Debug, Eq, Hash, PartialEq)]
    pub enum StoredShape<E, S, K = <E as Expression>::Atom>
    where
        E: Expression,
    {
        /// Key
        Key(K),

        /// Expression Shape
        Shape(S),

        #[doc(hidden)]
        __(util::Nothing<E>),
    }

    impl<E, S, K> StoredShape<E, S, K>
    where
        E: Expression,
    {
        /// Checks if the `StoredShape` is a key.
        #[must_use]
        #[inline]
        pub fn is_key(&self) -> bool {
            matches!(self, Self::Key(_))
        }

        /// Checks if the `StoredShape` is a shaped expression.
        #[must_use]
        #[inline]
        pub fn is_shape(&self) -> bool {
            matches!(self, Self::Shape(_))
        }

        /// Converts from an `StoredShape<E, S, K>` to an `Option<K>`.
        #[must_use]
        #[inline]
        pub fn key(self) -> Option<K> {
            match self {
                Self::Key(key) => Some(key),
                _ => None,
            }
        }

        /// Converts from an `&StoredShape<E, S, K>` to an `Option<&K>`.
        #[must_use]
        #[inline]
        pub fn key_ref(&self) -> Option<&K> {
            match self {
                Self::Key(key) => Some(key),
                _ => None,
            }
        }

        /// Converts from a `StoredShape<E, S, K>` to an `Option<S>`.
        #[must_use]
        #[inline]
        pub fn shape(self) -> Option<S> {
            match self {
                Self::Shape(shape) => Some(shape),
                _ => None,
            }
        }

        /// Converts from a `&StoredShape<E, S, K>` to an `Option<&S>`.
        #[must_use]
        #[inline]
        pub fn shape_ref(&self) -> Option<&S> {
            match self {
                Self::Shape(shape) => Some(shape),
                _ => None,
            }
        }

        /// Returns the contained `K` key, consuming the `self` value.
        ///
        /// # Panics
        ///
        /// Panics if the contained value was a `Shape`.
        #[inline]
        #[track_caller]
        pub fn unwrap_key(self) -> K {
            match self {
                Self::Key(key) => key,
                _ => panic!(),
            }
        }

        /// Returns the contained `Shape`, consuming the `self` value.
        ///
        /// # Panics
        ///
        /// Panics if the contained value was a `K`.
        #[inline]
        #[track_caller]
        pub fn unwrap_shape(self) -> S {
            match self {
                Self::Shape(shape) => shape,
                _ => panic!(),
            }
        }
    }

    impl<E, S, K> Clone for StoredShape<E, S, K>
    where
        E: Expression,
        S: Clone,
        K: Clone,
    {
        #[inline]
        fn clone(&self) -> Self {
            match self {
                Self::Key(key) => Self::Key(key.clone()),
                Self::Shape(shape) => Self::Shape(shape.clone()),
            }
        }
    }

    impl<E, S, K> From<StoredShape<E, S, K>> for Expr<E>
    where
        E: Expression,
        S: Into<Expr<E>>,
        K: Into<E::Atom>,
    {
        #[inline]
        fn from(expr: StoredShape<E, S, K>) -> Self {
            match expr {
                StoredShape::Key(key) => Self::Atom(key.into()),
                StoredShape::Shape(shape) => shape.into(),
            }
        }
    }

    /// [`StoredShape`] Matcher Error
    pub enum StoredShapeMatcherError<E, S, K = <E as Expression>::Atom>
    where
        E: Expression,
        S: Matcher<E>,
        K: TryFrom<E::Atom>,
    {
        /// Base Shape Error
        Base(<S as Matcher<E>>::Error),

        /// Invalid Key Error
        InvalidKey(K::Error),
    }

    impl<E, S, K> TryFrom<Expr<E>> for StoredShape<E, S, K>
    where
        E: Expression,
        S: Shape<E>,
        K: TryFrom<E::Atom>,
    {
        type Error = StoredShapeMatcherError<E, S, K>;

        #[inline]
        fn try_from(expr: Expr<E>) -> Result<Self, Self::Error> {
            match expr {
                Expr::Atom(key) => key
                    .try_into()
                    .map(StoredShape::Key)
                    .map_err(StoredShapeMatcherError::InvalidKey),
                _ => expr
                    .try_into()
                    .map(StoredShape::Shape)
                    .map_err(StoredShapeMatcherError::Base),
            }
        }
    }

    impl<E, S> Matcher<E> for StoredShape<E, S>
    where
        E: Expression,
        S: Matcher<E>,
    {
        type Error = StoredShapeMatcherError<E, S>;

        #[inline]
        fn matches_atom(atom: &E::Atom) -> Result<(), Self::Error> {
            let _ = atom;
            Ok(())
        }

        #[inline]
        fn matches_group(group: GroupRef<E>) -> Result<(), Self::Error> {
            S::matches_group(group).map_err(StoredShapeMatcherError::Base)
        }
    }

    impl<E, S> Shape<E> for StoredShape<E, S>
    where
        E: Expression,
        S: Shape<E>,
    {
    }

    impl<E, S, K> Resolvable<K> for StoredShape<E, S, K>
    where
        E: Expression,
    {
        type Part = S;

        type Output = S;

        type UnresolvedKeys = Result<K, Infallible>;

        #[inline]
        fn resolve<F>(self, mut resolver: F) -> Result<Self::Output, Self::UnresolvedKeys>
        where
            F: FnMut(&K) -> Option<Self::Part>,
        {
            match self {
                Self::Key(key) => resolver(&key).ok_or(Ok(key)),
                Self::Shape(shape) => Ok(shape),
            }
        }
    }
}

/// Utilities
pub mod util {
    use {
        alloc::vec::Vec,
        bitvec::vec::BitVec,
        core::{
            convert::Infallible,
            iter::{from_fn, FromIterator, FusedIterator},
            marker::PhantomData,
        },
    };

    /// An Infallible Phantom Data Object
    // FIXME: implement derive traits correctly
    #[derive(Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
    pub struct Nothing<T: ?Sized>(pub Infallible, PhantomData<T>);

    impl<T: ?Sized> Clone for Nothing<T> {
        #[inline]
        fn clone(&self) -> Self {
            Self(self.0, self.1)
        }
    }

    impl<T: ?Sized> Copy for Nothing<T> {}

    /// Builds a zeroed [`BitVec`] of the specified length.
    #[inline]
    pub fn zeroed_bit_vector(length: usize) -> BitVec {
        let mut matches: BitVec = BitVec::with_capacity(length);
        matches.resize(length, false);
        matches
    }

    /// Finds first match which is not already annotated in the [`BitVec`].
    #[inline]
    pub fn find_first_new_match_by<T, I, F>(
        needle: &T,
        haystack: I,
        matches: &BitVec,
        mut eq: F,
    ) -> Option<usize>
    where
        I: Iterator,
        F: FnMut(&T, I::Item) -> bool,
    {
        haystack
            .enumerate()
            .position(move |(i, elem)| eq(needle, elem) && !matches[i])
    }

    /// Looks for the first new match of the `needle` in the `haystack` and updates the `matches`.
    #[inline]
    pub fn set_first_new_match_by<T, H, F>(
        needle: &T,
        haystack: &[H],
        matches: &mut BitVec,
        eq: F,
    ) -> bool
    where
        F: FnMut(&T, &H) -> bool,
    {
        match find_first_new_match_by(needle, haystack.iter(), matches, eq) {
            Some(index) => {
                matches.set(index, true);
                false
            }
            _ => true,
        }
    }

    /// Skips over elements of the [`Iterator`] if their index is present in the [`BitVec`].
    #[inline]
    pub fn skip_matches<I>(iter: I, matches: BitVec) -> impl Iterator<Item = I::Item>
    where
        I: IntoIterator,
    {
        iter.into_iter()
            .enumerate()
            .filter_map(move |(i, elem)| Some(elem).filter(|_| !matches[i]))
    }

    /// Computes the symmetric difference of two multisets.
    pub fn multiset_symmetric_difference_by<L, RItem, F, OL>(
        left: L,
        right: Vec<RItem>,
        mut eq: F,
    ) -> (OL, impl Iterator<Item = RItem>)
    where
        L: IntoIterator,
        OL: FromIterator<L::Item>,
        F: FnMut(&L::Item, &RItem) -> bool,
    {
        let mut matches = zeroed_bit_vector(right.len());
        (
            left.into_iter()
                .filter(|l| set_first_new_match_by(l, &right, &mut matches, &mut eq))
                .collect(),
            skip_matches(right, matches),
        )
    }

    /// Computes the symmetric difference of two multisets.
    #[inline]
    pub fn multiset_symmetric_difference<L, RItem, OL>(
        left: L,
        right: Vec<RItem>,
    ) -> (OL, impl Iterator<Item = RItem>)
    where
        L: IntoIterator,
        L::Item: PartialEq<RItem>,
        OL: FromIterator<L::Item>,
    {
        multiset_symmetric_difference_by(left, right, PartialEq::eq)
    }

    /// Parallel Computation Utilities
    #[cfg(feature = "parallel")]
    #[cfg_attr(docsrs, doc(cfg(feature = "parallel")))]
    pub mod parallel {
        use {
            super::*,
            parking_lot::RwLock,
            rayon::iter::{
                FromParallelIterator, IndexedParallelIterator, IntoParallelIterator,
                IntoParallelRefIterator, ParallelIterator,
            },
        };

        /// Parallel Container Helper Trait
        pub trait ParallelContainer<T>:
            FromParallelIterator<T> + IntoParallelIterator<Item = T>
        where
            T: Send,
        {
        }

        impl<T, C> ParallelContainer<T> for C
        where
            T: Send,
            C: FromParallelIterator<T> + IntoParallelIterator<Item = T>,
        {
        }

        /// Locked [`BitVec`] Type
        pub type LockedBitVec = RwLock<BitVec>;

        /// Finds first match which is not already annotated in the [`BitVec`].
        #[inline]
        pub fn find_first_new_match_by<T, I, F>(
            needle: &T,
            haystack: I,
            matches: &LockedBitVec,
            eq: F,
        ) -> Option<usize>
        where
            T: Sync,
            I: IndexedParallelIterator,
            F: Send + Sync + Fn(&T, I::Item) -> bool,
        {
            haystack
                .enumerate()
                .position_first(move |(i, elem)| eq(needle, elem) && !matches.read()[i])
        }

        /// Looks for the first new match of the `needle` in the `haystack` and updates the `matches`.
        #[inline]
        pub fn set_first_new_match_by<T, H, F>(
            needle: &T,
            haystack: &[H],
            matches: &LockedBitVec,
            eq: F,
        ) -> bool
        where
            T: Sync,
            H: Sync,
            F: Send + Sync + Fn(&T, &H) -> bool,
        {
            match find_first_new_match_by(needle, haystack.par_iter(), matches, eq) {
                Some(index) => {
                    matches.write().set(index, true);
                    false
                }
                _ => true,
            }
        }

        /// Skips over elements of the [`ParallelIterator`] if their index is present in the [`BitVec`].
        #[inline]
        pub fn skip_matches<I>(iter: I, matches: BitVec) -> impl ParallelIterator<Item = I::Item>
        where
            I: IntoParallelIterator,
            I::Iter: IndexedParallelIterator,
        {
            iter.into_par_iter()
                .enumerate()
                .filter_map(move |(i, elem)| Some(elem).filter(|_| !matches[i]))
        }

        /// Computes the symmetric difference of two multisets.
        pub fn multiset_symmetric_difference_by<L, RItem, F, OL>(
            left: L,
            right: Vec<RItem>,
            eq: F,
        ) -> (OL, impl ParallelIterator<Item = RItem>)
        where
            L: IntoParallelIterator,
            L::Item: Sync,
            RItem: Send + Sync,
            OL: FromParallelIterator<L::Item>,
            F: Send + Sync + Fn(&L::Item, &RItem) -> bool,
        {
            let matches = RwLock::new(zeroed_bit_vector(right.len()));
            (
                left.into_par_iter()
                    .filter(|l| set_first_new_match_by(l, &right, &matches, &eq))
                    .collect(),
                skip_matches(right, matches.into_inner()),
            )
        }

        /// Computes the symmetric difference of two multisets.
        #[inline]
        pub fn multiset_symmetric_difference<L, RItem, OL>(
            left: L,
            right: Vec<RItem>,
        ) -> (OL, impl ParallelIterator<Item = RItem>)
        where
            L: IntoParallelIterator,
            L::Item: Sync + PartialEq<RItem>,
            RItem: Send + Sync,
            OL: FromParallelIterator<L::Item>,
        {
            multiset_symmetric_difference_by(left, right, PartialEq::eq)
        }
    }

    /// Checks if the two multisets share any elements.
    #[inline]
    pub fn has_intersection<L, RItem>(left: L, right: &[&RItem]) -> bool
    where
        L: IntoIterator,
        L::Item: PartialEq<RItem>,
    {
        has_intersection_by(left, right, PartialEq::eq)
    }

    /// Checks if the two multisets share any elements.
    pub fn has_intersection_by<L, RItem, F>(left: L, right: &[&RItem], mut eq: F) -> bool
    where
        L: IntoIterator,
        F: FnMut(&L::Item, &RItem) -> bool,
    {
        left.into_iter()
            .any(move |l| right.iter().all(|r| eq(&l, r)))
    }

    /// Generates a two item iterator.
    #[inline]
    pub fn two_item_iter<T>(fst: T, snd: T) -> impl Iterator<Item = T> {
        Some(fst).into_iter().chain(Some(snd))
    }

    /// Generates an iterator that returns in pairs or returns `Some(None)` if a pair could not be formed.
    #[inline]
    pub fn by_pairs<T, I>(iter: I) -> impl FusedIterator<Item = Option<(T, T)>>
    where
        I: IntoIterator<Item = T>,
    {
        let mut iter = iter.into_iter();
        from_fn(move || match iter.next() {
            Some(fst) => match iter.next() {
                Some(snd) => Some(Some((fst, snd))),
                _ => Some(None),
            },
            _ => None,
        })
        .fuse()
    }
}

//! Rational Deduction
//!
//! _Rust implementation of the rational deduction algorithms_.

#![cfg_attr(docsrs, feature(doc_cfg), deny(broken_intra_doc_links))]
#![feature(generic_associated_types)]
#![feature(exhaustive_patterns)]
#![allow(incomplete_features)]
#![forbid(unsafe_code)]
#![no_std]

// FIXME: reimplement all of the incorrect `derive` traits
// TODO: implement `Deref/Borrow/ToOwned` traits where possible

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
            self, Expr, ExprRef, Expression, Group, GroupRef, GroupRefItem, GroupReference,
            Reference,
        },
    };
}

pub use prelude::*;

/// Container Helper Trait
pub trait Container<T>: FromIterator<T> + IntoIterator<Item = T> {}

impl<T, C> Container<T> for C where C: FromIterator<T> + IntoIterator<Item = T> {}

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

    /// Converts `self` into an instance of `E: Expression`.
    #[inline]
    fn into(self) -> E
    where
        Self: Sized,
    {
        E::from_expr(self.structure().into())
    }

    /// Tries to build `Self` from an instance of `E: Expression`.
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

/// Rule Module
pub mod rule {
    use super::*;

    /// Composes two rules using the ratio monoid multiplication algorithm.
    #[inline]
    pub fn pair_compose<E, T, B, Output>(top: T, bot: B) -> Output
    where
        E: Expression,
        E::Atom: PartialEq,
        E::Group: FromIterator<E> + IntoIterator<Item = E>,
        T: Rule<E>,
        B: Rule<E>,
        Output: Rule<E>,
    {
        pair_compose_by(top, bot, E::eq)
    }

    /// Composes two rules using the ratio monoid multiplication algorithm.
    pub fn pair_compose_by<E, T, B, Output, F>(top: T, bot: B, eq: F) -> Output
    where
        E: Expression,
        E::Group: FromIterator<E> + IntoIterator<Item = E>,
        T: Rule<E>,
        B: Rule<E>,
        Output: Rule<E>,
        F: FnMut(&E, &E) -> bool,
    {
        let top = top.structure();
        let bot = bot.structure();
        let (lower, upper) = util::multiset_symmetric_difference_by::<_, _, E::Group, _>(
            top.bot,
            bot.top.into_iter().collect(),
            eq,
        );
        Output::from(Structure::new(
            upper.chain(top.top).collect(),
            lower.into_iter().chain(bot.bot).collect(),
        ))
    }

    /// Fold an iterator of rules using [`pair_compose`].
    #[inline]
    pub fn compose<E, R, I>(rules: I) -> R
    where
        E: Expression,
        E::Atom: PartialEq,
        E::Group: FromIterator<E> + IntoIterator<Item = E>,
        R: Rule<E>,
        I: IntoIterator<Item = R>,
    {
        compose_by(rules, E::eq)
    }

    /// Fold an iterator of rules using [`pair_compose_by`].
    #[inline]
    pub fn compose_by<E, R, I, F>(rules: I, mut eq: F) -> R
    where
        E: Expression,
        E::Group: FromIterator<E> + IntoIterator<Item = E>,
        R: Rule<E>,
        I: IntoIterator<Item = R>,
        F: FnMut(&E, &E) -> bool,
    {
        let mut iter = rules.into_iter();
        iter.next()
            .map(move |r| iter.fold(r, move |t, b| pair_compose_by(t, b, &mut eq)))
            .unwrap_or_else(R::empty)
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
        E::Group: FromIterator<E> + IntoIterator<Item = E>,
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

        /// Clones a rule.
        #[inline]
        fn clone(&self) -> Self
        where
            Self: Sized,
            E::Atom: Clone,
            E::Group: FromIterator<E>,
        {
            Self::from(Clone::clone(&Structure::from(self.cases())))
        }

        /// Builds a new `Rule` from two groups.
        #[inline]
        fn new(top: E::Group, bot: E::Group) -> Self
        where
            Self: Sized,
        {
            Self::from(Structure::new(top, bot))
        }

        /// Builds an empty `Rule`.
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
            // TODO: what about more general substitution methods
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
            // TODO: what about more general substitution methods
            Self::new(
                substitution.apply_group_ref(&self.top()),
                substitution.apply_group_ref(&self.bot()),
            )
        }
    }

    /// Rule Reference Structure Type
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
        /// Builds a new `Reference` from references to the top and bottom of a rule.
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
            Self::new(structure.top.reference(), structure.bot.reference())
        }
    }

    /// Based Rule Reference Structure Type
    pub struct BasedReference<'e, E>
    where
        E: 'e + Expression,
    {
        /// Base Group Reference
        pub base: GroupRef<'e, E>,
    }

    impl<'e, E> BasedReference<'e, E>
    where
        E: Expression,
    {
        /// Builds a new `BasedReference` from a `base` group reference.
        ///
        /// # Safety
        ///
        /// This function does not perform any checks to ensure that the `base` group reference
        /// points to a valid `Rule` structure. The `BasedReference::top` and `BasedReference::bot`
        /// methods will panic if the `base` reference is not valid.
        #[inline]
        pub fn new(base: GroupRef<'e, E>) -> Self {
            Self { base }
        }

        /// Returns the top element of the rule.
        ///
        /// # Panics
        ///
        /// This function panics if the `self.base` reference does not point to a valid rule object.
        #[inline]
        pub fn top(&self) -> GroupRef<E> {
            self.ref_pair().0
        }

        /// Returns the bottom element of the rule.
        ///
        /// # Panics
        ///
        /// This function panics if the `self.base` reference does not point to a valid rule object.
        #[inline]
        pub fn bot(&self) -> GroupRef<E> {
            self.ref_pair().1
        }

        /// Returns the top and bottom element of the rule as a pair.
        ///
        /// # Panics
        ///
        /// This function panics if the `self.base` reference does not point to a valid rule object.
        #[inline]
        pub fn ref_pair(&self) -> RefPair<E> {
            // FIXME: use `unwrap_unchecked` when it comes out
            let mut iter = self.base.iter();
            (
                iter.next().unwrap().unwrap_group(),
                iter.next().unwrap().unwrap_group(),
            )
        }
    }

    impl<'e, E> Clone for BasedReference<'e, E>
    where
        E: Expression,
        GroupRef<'e, E>: Clone,
    {
        #[inline]
        fn clone(&self) -> Self {
            Self::new(self.base.clone())
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
            Ok(Self::new(expr.unwrap_group()))
        }
    }

    /// Rule Structure Type
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
        /// Builds a new `Structure` from a pair of groups.
        #[inline]
        pub fn new(top: E::Group, bot: E::Group) -> Self {
            Self { top, bot }
        }

        /// Returns the `Structure` as a `Pair`.
        #[inline]
        pub fn pair(self) -> Pair<E> {
            (self.top, self.bot)
        }

        /// Returns the `Structure` as a pair of references.
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
            Self::new(E::Group::from_iter(None), E::Group::from_iter(None))
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

    /// Rule Structure Error Type
    #[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
    pub enum StructureError {
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

    /// Checks if an atom matches the `Rule` pattern.
    #[inline]
    pub fn matches_atom<E>(atom: &E::Atom) -> Result<(), StructureError>
    where
        E: Expression,
    {
        let _ = atom;
        Err(StructureError::NotGroup)
    }

    /// Checks if a group matches the `Rule` pattern.
    #[inline]
    pub fn matches_group<E>(group: &GroupRef<E>) -> Result<(), StructureError>
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
                (true, false) => Err(StructureError::MissingBotGroup),
                (false, true) => Err(StructureError::MissingTopGroup),
                _ => Err(StructureError::MissingTopBotGroups),
            },
            _ => Err(StructureError::BadGroupShape),
        }
    }

    /// Checks if an expression matches the `Rule` pattern.
    #[inline]
    pub fn matches<E>(expr: &ExprRef<E>) -> Result<(), StructureError>
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
        type Error = StructureError;

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
        E::Group: FromIterator<E> + IntoIterator<Item = E>,
    {
    }

    impl<E> Rule<E> for Structure<E>
    where
        E: Expression,
        E::Group: FromIterator<E> + IntoIterator<Item = E>,
    {
        #[inline]
        fn cases(&self) -> Reference<E> {
            self.into()
        }
    }

    /// Rule Reference Pair Type
    pub type RefPair<'e, E> = (GroupRef<'e, E>, GroupRef<'e, E>);

    /// Rule Pair Type
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
        E::Group: FromIterator<E> + IntoIterator<Item = E>,
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
        E::Group: FromIterator<E> + IntoIterator<Item = E>,
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

        /// Returns an owned `Term`.
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

        /// Returns the `&Term` as a `TermRef`.
        #[inline]
        pub fn as_ref(&self) -> TermRef<'_, E> {
            TermRef::new(&self.var, &self.expr)
        }

        /// Builds an identity `Term`.
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
                    mem::replace(&mut self.expr, E::default()).unwrap_atom(),
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
        E::Group: FromIterator<E> + IntoIterator<Item = E>,
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
            self.get_owned(&atom)
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
            E::Group: IntoIterator<Item = E> + FromIterator<E>,
        {
            expr.substitute(move |atom| self.apply_atom(atom))
        }

        /// Performs substitution on an expression by reference.
        #[inline]
        fn apply_ref(&self, expr: &E) -> E
        where
            E::Atom: Clone + PartialEq,
            E::Group: IntoIterator<Item = E> + FromIterator<E>,
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
        _marker: PhantomData<E>,
    }

    impl<E, V> Structure<E, V>
    where
        E: Expression,
        V: Container<Term<E>>,
    {
        /// Builds a new `Structure` from a `Term` container.
        #[inline]
        pub fn new(terms: V) -> Self {
            Self {
                terms,
                _marker: PhantomData,
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

    /// Substitution Structure Error Type
    #[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
    pub enum StructureError {
        /// The expression is not a group.
        NotGroup,

        /// The expression is not grouped in pairs.
        NotGroupedInPairs,

        /// The expression does not have the right group shape.
        // TODO: return all of `var` that were not atoms?
        BadGroupShape,
    }

    /// Checks if an atom matches the `Substitution` pattern.
    #[inline]
    pub fn matches_atom<E>(atom: &E::Atom) -> Result<(), StructureError>
    where
        E: Expression,
    {
        let _ = atom;
        Err(StructureError::NotGroup)
    }

    /// Checks if a group matches the `Substitution` pattern.
    #[inline]
    pub fn matches_group<E>(group: &GroupRef<E>) -> Result<(), StructureError>
    where
        E: Expression,
    {
        for pair in util::by_pairs(group.iter()) {
            match pair {
                Some((var, _)) => {
                    if !var.is_atom() {
                        return Err(StructureError::BadGroupShape);
                    }
                }
                _ => return Err(StructureError::NotGroupedInPairs),
            }
        }
        Ok(())
    }

    /// Checks if an expression matches the `Substitution` pattern.
    #[inline]
    pub fn matches<E>(expr: &ExprRef<E>) -> Result<(), StructureError>
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
        type Error = StructureError;

        #[inline]
        fn matches_atom(atom: &E::Atom) -> Result<(), Self::Error> {
            matches_atom::<E>(atom)
        }

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
                .map(move |pair| match pair {
                    Some(pair) => pair.try_into().map_err(move |_| Self::Error::BadGroupShape),
                    _ => Err(Self::Error::NotGroupedInPairs),
                })
                .collect()
        }
    }

    impl<E, V> Shape<E> for Structure<E, V>
    where
        E: Expression,
        E::Group: FromIterator<E> + IntoIterator<Item = E>,
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
        E::Group: FromIterator<E> + IntoIterator<Item = E>,
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

    /// Stored Shape Type
    #[derive(Copy, Debug, Eq, Hash, PartialEq)]
    pub enum StoredShape<E, S>
    where
        E: Expression,
        S: Shape<E>,
    {
        /// Atomic Key
        Key(E::Atom),

        /// Expression Shape
        Shape(S),
    }

    impl<E, S> StoredShape<E, S>
    where
        E: Expression,
        S: Shape<E>,
    {
        /// Checks if the `StoredShape` is an atomic key.
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

        /// Converts from an `StoredShape<E, _>` to an `Option<E::Atom>`.
        #[must_use]
        #[inline]
        pub fn key(self) -> Option<E::Atom> {
            match self {
                Self::Key(key) => Some(key),
                _ => None,
            }
        }

        /// Converts from an `&StoredShape<E, _>` to an `Option<&E::Atom>`.
        #[must_use]
        #[inline]
        pub fn key_ref(&self) -> Option<&E::Atom> {
            match self {
                Self::Key(key) => Some(key),
                _ => None,
            }
        }

        /// Converts from a `StoredShape<_, S>` to an `Option<S>`.
        #[must_use]
        #[inline]
        pub fn shape(self) -> Option<S> {
            match self {
                Self::Shape(shape) => Some(shape),
                _ => None,
            }
        }

        /// Converts from a `&StoredShape<_, S>` to an `Option<&S>`.
        #[must_use]
        #[inline]
        pub fn shape_ref(&self) -> Option<&S> {
            match self {
                Self::Shape(shape) => Some(shape),
                _ => None,
            }
        }

        /// Returns the contained `E::Atom` key, consuming the `self` value.
        ///
        /// # Panics
        ///
        /// Panics if the contained value was a `Shape`.
        #[inline]
        #[track_caller]
        pub fn unwrap_key(self) -> E::Atom {
            match self {
                Self::Key(atom) => atom,
                _ => panic!(),
            }
        }

        /// Returns the contained `Shape`, consuming the `self` value.
        ///
        /// # Panics
        ///
        /// Panics if the contained value was an `E::Atom`.
        #[inline]
        #[track_caller]
        pub fn unwrap_shape(self) -> S {
            match self {
                Self::Shape(shape) => shape,
                _ => panic!(),
            }
        }
    }

    impl<E, S> Resolvable<E::Atom> for StoredShape<E, S>
    where
        E: Expression,
        S: Shape<E>,
    {
        type Part = S;

        type Output = S;

        type UnresolvedKeys = Result<E::Atom, Infallible>;

        #[inline]
        fn resolve<F>(self, mut resolver: F) -> Result<Self::Output, Self::UnresolvedKeys>
        where
            F: FnMut(&E::Atom) -> Option<Self::Part>,
        {
            match self {
                Self::Key(key) => resolver(&key).ok_or(Ok(key)),
                Self::Shape(shape) => Ok(shape),
            }
        }
    }

    impl<E, S> Clone for StoredShape<E, S>
    where
        E: Expression,
        E::Atom: Clone,
        S: Clone + Shape<E>,
    {
        #[inline]
        fn clone(&self) -> Self {
            match self {
                Self::Key(key) => Self::Key(key.clone()),
                Self::Shape(shape) => Self::Shape(shape.clone()),
            }
        }
    }

    impl<E, S> From<StoredShape<E, S>> for Expr<E>
    where
        E: Expression,
        S: Shape<E>,
    {
        #[inline]
        fn from(expr: StoredShape<E, S>) -> Self {
            match expr {
                StoredShape::Key(key) => Self::Atom(key),
                StoredShape::Shape(shape) => shape.into(),
            }
        }
    }

    impl<E, S> TryFrom<Expr<E>> for StoredShape<E, S>
    where
        E: Expression,
        S: Shape<E>,
    {
        type Error = <S as Matcher<E>>::Error;

        #[inline]
        fn try_from(expr: Expr<E>) -> Result<Self, Self::Error> {
            match expr {
                Expr::Atom(key) => Ok(StoredShape::Key(key)),
                _ => expr.try_into().map(StoredShape::Shape),
            }
        }
    }

    impl<E, S> Matcher<E> for StoredShape<E, S>
    where
        E: Expression,
        S: Shape<E>,
    {
        type Error = <S as Matcher<E>>::Error;

        #[inline]
        fn matches_atom(atom: &E::Atom) -> Result<(), Self::Error> {
            let _ = atom;
            Ok(())
        }

        #[inline]
        fn matches_group(group: GroupRef<E>) -> Result<(), Self::Error> {
            S::matches_group(group)
        }
    }

    impl<E, S> Shape<E> for StoredShape<E, S>
    where
        E: Expression,
        S: Shape<E>,
    {
    }
}

/// Utilities
pub mod util {
    use {alloc::vec::Vec, bitvec::vec::BitVec, core::iter::FromIterator};

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

    /// Computes the symmetric difference of two multisets.
    pub fn multiset_symmetric_difference_by<L, RItem, OL, F>(
        left: L,
        right: Vec<RItem>,
        mut eq: F,
    ) -> (OL, impl Iterator<Item = RItem>)
    where
        L: IntoIterator,
        OL: FromIterator<L::Item>,
        F: FnMut(&L::Item, &RItem) -> bool,
    {
        let right_len = right.len();
        let mut matched_indices: BitVec = BitVec::with_capacity(right_len);
        matched_indices.resize(right_len, false);
        (
            left.into_iter()
                .filter(|l| {
                    (&right).iter().enumerate().all(|(i, r)| {
                        if eq(l, r) && !matched_indices[i] {
                            matched_indices.set(i, true);
                            return false;
                        }
                        true
                    })
                })
                .collect(),
            right
                .into_iter()
                .zip(matched_indices)
                .filter_map(move |(r, m)| Some(r).filter(move |_| !m)),
        )
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
    pub fn by_pairs<T, I>(iter: I) -> impl Iterator<Item = Option<(T, T)>>
    where
        I: IntoIterator<Item = T>,
    {
        let mut iter = iter.into_iter();
        core::iter::from_fn(move || match iter.next() {
            Some(fst) => match iter.next() {
                Some(snd) => Some(Some((fst, snd))),
                _ => Some(None),
            },
            _ => None,
        })
        .fuse()
    }
}

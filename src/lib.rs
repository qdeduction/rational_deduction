//! Rational Deduction Algorithm

#![cfg_attr(docsrs, feature(doc_cfg), deny(broken_intra_doc_links))]
#![feature(generic_associated_types)]
#![feature(exhaustive_patterns)]
#![allow(incomplete_features)]
#![forbid(unsafe_code)]
#![no_std]

// FIXME: reimplement all of the incorrect `derive` traits

extern crate alloc;

use {
    core::{
        borrow::Borrow,
        convert::{Infallible, TryFrom, TryInto},
        iter::FromIterator,
        marker::PhantomData,
    },
    exprz::{
        iter::{IntoIteratorGen, IteratorGen},
        shape::{Matcher, Shape},
    },
};

/// Package Version
pub const VERSION: &str = env!("CARGO_PKG_VERSION");

/// Re-Exported Objects
pub use {
    exprz::{self, Expr, ExprRef, Expression},
    rule::Rule,
    substitution::Substitution,
};

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
    fn into(self) -> E
    where
        Self: Sized,
    {
        E::from_expr(self.structure().into())
    }

    /// Tries to build `Self` from an instance of `E: Expression`.
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
            .unwrap_or_else(R::default)
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
        fn top(&self) -> <E::Group as IntoIteratorGen<E>>::IterGen<'_> {
            self.cases().top
        }

        /// Returns a reference to the bottom element of the rule.
        fn bot(&self) -> <E::Group as IntoIteratorGen<E>>::IterGen<'_> {
            self.cases().bot
        }

        /// Returns `true` if two rules are equal.
        fn eq<R>(&self, other: &R) -> bool
        where
            E::Atom: PartialEq,
            R: Rule<E>,
        {
            self.cases().eq(&other.cases())
        }

        /// Clones a rule.
        fn clone(&self) -> Self
        where
            Self: Sized,
            E::Atom: Clone,
            E::Group: FromIterator<E>,
        {
            Self::from(Clone::clone(&Structure::from(self.cases())))
        }

        /// Builds a new `Rule` from two groups.
        fn new(top: E::Group, bot: E::Group) -> Self
        where
            Self: Sized,
        {
            Self::from(Structure::new(top, bot))
        }

        /// Builds the default `Rule`.
        fn default() -> Self
        where
            Self: Sized,
        {
            Self::from(Default::default())
        }

        /// Returns the top and bottom element of the rule as a pair.
        fn pair(self) -> (E::Group, E::Group)
        where
            Self: Sized,
        {
            let Structure { top, bot } = self.structure();
            (top, bot)
        }
    }

    /// Rule Reference Structure Type
    pub struct Reference<'e, E>
    where
        E: 'e + Expression,
    {
        /// Top element of the rule
        pub top: <E::Group as IntoIteratorGen<E>>::IterGen<'e>,

        /// Bottom element of the rule
        pub bot: <E::Group as IntoIteratorGen<E>>::IterGen<'e>,
    }

    impl<'e, E> Reference<'e, E>
    where
        E: Expression,
    {
        /// Builds a new `Reference` from references to the top and bottom of a rule.
        #[inline]
        pub fn new(
            top: <E::Group as IntoIteratorGen<E>>::IterGen<'e>,
            bot: <E::Group as IntoIteratorGen<E>>::IterGen<'e>,
        ) -> Self {
            Self { top, bot }
        }
    }

    impl<'e, E> PartialEq for Reference<'e, E>
    where
        E: 'e + Expression,
        E::Atom: PartialEq,
    {
        #[inline]
        fn eq(&self, other: &Self) -> bool {
            ExprRef::<E>::eq_groups::<E>(&self.top, &other.top)
                && ExprRef::<E>::eq_groups::<E>(&self.bot, &other.bot)
        }
    }

    impl<'e, E> Eq for Reference<'e, E>
    where
        E: Expression,
        E::Atom: PartialEq,
    {
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

    impl<'e, E> From<Reference<'e, E>> for Structure<E>
    where
        E: 'e + Expression,
        E::Atom: Clone,
        E::Group: FromIterator<E>,
    {
        #[must_use]
        #[inline]
        fn from(reference: Reference<'e, E>) -> Self {
            // FIXME: move this "algorithm" to `ExprZ`
            Self::new(
                reference
                    .top
                    .iter()
                    .map(move |e| e.borrow().clone())
                    .collect(),
                reference
                    .bot
                    .iter()
                    .map(move |e| e.borrow().clone())
                    .collect(),
            )
        }
    }

    impl<'e, E> From<&'e Structure<E>> for Reference<'e, E>
    where
        E: Expression,
    {
        #[inline]
        fn from(reference: &'e Structure<E>) -> Self {
            Self::new(reference.top.gen(), reference.bot.gen())
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

    impl<E> Eq for Structure<E>
    where
        E: Expression,
        E::Atom: PartialEq,
    {
    }

    impl<E> From<Structure<E>> for Expr<E>
    where
        E: Expression,
        E::Group: FromIterator<E>,
    {
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

    impl<E> Matcher<E> for Structure<E>
    where
        E: Expression,
    {
        type Error = StructureError;

        #[inline]
        fn matches_atom(atom: &E::Atom) -> Result<(), Self::Error> {
            let _ = atom;
            Err(Self::Error::NotGroup)
        }

        #[inline]
        fn matches_group(
            group: <E::Group as IntoIteratorGen<E>>::IterGen<'_>,
        ) -> Result<(), Self::Error> {
            let mut iter = group.iter();
            match (iter.next(), iter.next(), iter.next()) {
                (Some(top), Some(bot), None) => {
                    match (top.borrow().is_group(), bot.borrow().is_group()) {
                        (true, true) => Ok(()),
                        (true, false) => Err(Self::Error::MissingBotGroup),
                        (false, true) => Err(Self::Error::MissingTopGroup),
                        _ => Err(Self::Error::MissingTopBotGroups),
                    }
                }
                _ => Err(Self::Error::BadGroupShape),
            }
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
}

/// Substitution Module
pub mod substitution {
    use {
        super::*,
        alloc::vec::Vec,
        core::{mem, slice},
    };

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
            self.expr
                .cases()
                .atom()
                .map_or(false, move |atom| atom == self.var)
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

        /// Checks if the `Substitution` is empty.
        #[inline]
        fn is_empty(&self) -> bool {
            self.iter().next().is_none()
        }

        /// Checks if all of the elements of `&self` are the identity substitution.
        #[inline]
        fn is_identity(&self) -> bool
        where
            E::Atom: PartialEq,
        {
            self.iter().all(move |t| t.is_identity())
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
        fn get_new(&self, var: &E::Atom) -> Option<E>
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
            self.get_new(&atom)
                .unwrap_or_else(move || E::from_atom(atom))
        }

        /// Performs substitution on an atomic expression by reference.
        #[inline]
        fn apply_atom_ref(&self, atom: &E::Atom) -> E
        where
            E::Atom: Clone + PartialEq,
            E::Group: FromIterator<E>,
        {
            self.get_new(&atom)
                .unwrap_or_else(move || E::from_atom(atom.clone()))
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

        /// Tries to generate a substitution from two expressions.
        #[inline]
        fn generate<F>(lhs: &E, rhs: &E, mut can_substitute: F) -> Option<Directed<Self>>
        where
            Self: Sized,
            E::Atom: Clone + PartialEq,
            F: FnMut(&E::Atom) -> bool,
        {
            generate::<_, Structure<_, V>, _>(lhs, rhs, &mut can_substitute)
                .map(move |d| d.map(Self::from))
        }
    }

    /// Substitution Structure Type
    #[derive(Clone, Copy, Debug, Default, Eq, Hash, PartialEq)]
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
        // TODO: return all of `var` that were not atoms
        BadGroupShape,
    }

    impl<E, V> Matcher<E> for Structure<E, V>
    where
        E: Expression,
        V: Container<Term<E>>,
    {
        type Error = StructureError;

        #[inline]
        fn matches_atom(atom: &E::Atom) -> Result<(), Self::Error> {
            let _ = atom;
            Err(Self::Error::NotGroup)
        }

        fn matches_group(
            group: <E::Group as IntoIteratorGen<E>>::IterGen<'_>,
        ) -> Result<(), Self::Error> {
            for pair in util::by_pairs(group.iter()) {
                match pair {
                    Some((var, _)) => {
                        if !var.borrow().is_atom() {
                            return Err(Self::Error::BadGroupShape);
                        }
                    }
                    _ => return Err(Self::Error::NotGroupedInPairs),
                }
            }
            Ok(())
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
    pub struct StructureVecIter<'s, E>
    where
        E: Expression,
    {
        iter: slice::Iter<'s, Term<E>>,
    }

    impl<'s, E> StructureVecIter<'s, E>
    where
        E: Expression,
    {
        #[inline]
        fn new(structure: &'s Structure<E>) -> Self {
            Self {
                iter: structure.terms.iter(),
            }
        }
    }

    impl<'s, E> Iterator for StructureVecIter<'s, E>
    where
        E: Expression,
    {
        type Item = TermRef<'s, E>;

        #[inline]
        fn next(&mut self) -> Option<Self::Item> {
            self.iter.next().map(Term::as_ref)
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
            StructureVecIter::new(self)
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

        /// Returns `Some` with the inner substitution if `self` is `Backward`.
        #[must_use]
        #[inline]
        pub fn backward(self) -> Option<S> {
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

    /// Tries to generate a substitution from two expressions.
    pub fn generate<E, S, F>(lhs: &E, rhs: &E, can_substitute: &mut F) -> Option<Directed<S>>
    where
        E: Expression,
        E::Atom: Clone + PartialEq,
        E::Group: FromIterator<E>,
        S: FromIterator<Term<E>> + IntoIterator<Item = Term<E>>,
        F: FnMut(&E::Atom) -> bool,
    {
        match (lhs.cases(), rhs.cases()) {
            (ExprRef::Atom(lhs_atom), ExprRef::Atom(rhs_atom)) => {
                if lhs_atom == rhs_atom {
                    Some(Directed::Forward(S::from_iter(None)))
                } else if can_substitute(lhs_atom) {
                    Some(Directed::Forward(
                        Term::new(lhs_atom.clone(), rhs.clone()).unit(),
                    ))
                } else if can_substitute(rhs_atom) {
                    Some(Directed::Backward(
                        Term::new(rhs_atom.clone(), lhs.clone()).unit(),
                    ))
                } else {
                    None
                }
            }
            (ExprRef::Atom(lhs), _) if can_substitute(lhs) => Some(Directed::Forward(
                Term::new(lhs.clone(), rhs.clone()).unit(),
            )),
            (_, ExprRef::Atom(rhs)) if can_substitute(rhs) => Some(Directed::Backward(
                Term::new(rhs.clone(), lhs.clone()).unit(),
            )),
            (ExprRef::Group(lhs), ExprRef::Group(rhs)) => {
                generate_from_groups(lhs, rhs, can_substitute)
            }
            _ => None,
        }
    }

    /// Tries to generate a substitution from two grouped expressions.
    pub fn generate_from_groups<E, S, F>(
        lhs: <E::Group as IntoIteratorGen<E>>::IterGen<'_>,
        rhs: <E::Group as IntoIteratorGen<E>>::IterGen<'_>,
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
            match generate::<_, S, _>(lhs.borrow(), rhs.borrow(), can_substitute) {
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

        /// Converts from a `StoredShape<_, S>` to an `Option<S>`.
        #[must_use]
        #[inline]
        pub fn shape(self) -> Option<S> {
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
        fn matches_group(
            group: <E::Group as IntoIteratorGen<E>>::IterGen<'_>,
        ) -> Result<(), Self::Error> {
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
    pub fn has_intersection<I>(left: I, right: Vec<&I::Item>) -> bool
    where
        I: IntoIterator,
        I::Item: PartialEq,
    {
        has_intersection_by(left, right, PartialEq::eq)
    }

    /// Checks if the two multisets share any elements.
    pub fn has_intersection_by<I, F>(left: I, right: Vec<&I::Item>, mut eq: F) -> bool
    where
        I: IntoIterator,
        F: FnMut(&I::Item, &I::Item) -> bool,
    {
        left.into_iter()
            .any(move |l| right.iter().all(|r| eq(&l, r)))
    }

    /// Generates a two item iterator.
    #[inline]
    pub fn two_item_iter<T>(fst: T, snd: T) -> impl Iterator<Item = T> {
        Some(fst).into_iter().chain(Some(snd))
    }

    /// Generate an iterator that returns in pairs or returns `Some(None)` if a pair could not be formed.
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

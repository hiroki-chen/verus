#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

// Use external_fn_specification on an external function from the same crate

test_verify_one_file! {
    #[test] test_basics verus_code! {
        #[verifier(external)]
        fn negate_bool(b: bool, x: u8) -> bool {
            !b
        }

        #[verifier(external_fn_specification)]
        fn negate_bool_requires_ensures(b: bool, x: u8) -> (ret_b: bool)
            requires x != 0,
            ensures ret_b == !b
        {
            negate_bool(b, x)
        }

        fn test1() {
            let ret_b = negate_bool(true, 1);
            assert(ret_b == false);
        }

        fn test2() {
            let ret_b = negate_bool(true, 0); // FAILS
        }

        fn test3() {
            let ret_b = negate_bool(true, 1);
            assert(ret_b == true); // FAILS
        }
    } => Err(err) => assert_fails(err, 2)
}

// Apply external_fn_specification on a function from an external crate
// don't import vstd for this test (it would cause overlap)

test_verify_one_file! {
    #[test] test_apply_spec_to_external verus_code! {
        #[verifier(external_fn_specification)]
        pub fn swap_requires_ensures<T>(a: &mut T, b: &mut T)
            ensures *a == *old(b), *b == *old(a),
        {
            std::mem::swap(a, b)
        }

        fn test1() {
            let mut x: u8 = 5;
            let mut y: u8 = 7;
            std::mem::swap(&mut x, &mut y);
            assert(x == 7 && y == 5);
        }

        fn test2() {
            let mut x: u8 = 5;
            let mut y: u8 = 7;
            std::mem::swap(&mut x, &mut y);
            assert(x == 5); // FAILS
        }
    } => Err(err) => assert_fails(err, 1)
}

// Import a specification from vstd of a function from std

test_verify_one_file! {
    #[test] test_import_spec_from_vstd verus_code! {
        use vstd::*;

        fn test1() {
            let mut x: u8 = 5;
            let mut y: u8 = 7;
            std::mem::swap(&mut x, &mut y);
            assert(x == 7 && y == 5);
        }

        fn test2() {
            let mut x: u8 = 5;
            let mut y: u8 = 7;
            std::mem::swap(&mut x, &mut y);
            assert(x == 5); // FAILS
        }
    } => Err(err) => assert_fails(err, 1)
}

// Test for overlap

test_verify_one_file! {
    #[test] test_overlap verus_code! {
        #[verifier(external)]
        fn negate_bool(b: bool, x: u8) -> bool {
            !b
        }

        #[verifier(external_fn_specification)]
        fn negate_bool_requires_ensures(b: bool, x: u8) -> (ret_b: bool)
            requires x != 0,
            ensures ret_b == !b
        {
            negate_bool(b, x)
        }

        #[verifier(external_fn_specification)]
        fn negate_bool_requires_ensures2(b: bool, x: u8) -> (ret_b: bool)
            requires x != 0,
            ensures ret_b == !b
        {
            negate_bool(b, x)
        }
    } => Err(err) => assert_vir_error_msg(err, "duplicate specification for `crate::negate_bool`")
}

test_verify_one_file! {
    #[test] test_overlap2 verus_code! {
        #[verifier(external_fn_specification)]
        pub fn swap_requires_ensures<T>(a: &mut T, b: &mut T)
            ensures *a == *old(b), *b == *old(a),
        {
            std::mem::swap(a, b)
        }

        #[verifier(external_fn_specification)]
        pub fn swap_requires_ensures2<T>(a: &mut T, b: &mut T)
            ensures *a == *old(b), *b == *old(a),
        {
            std::mem::swap(a, b)
        }
    } => Err(err) => assert_vir_error_msg(err, "duplicate specification for `core::mem::swap`")
}

test_verify_one_file! {
    #[test] test_overlap3 verus_code! {
        use vstd::*;

        // This will conflict with the mem::swap specification declared in vstd
        #[verifier(external_fn_specification)]
        pub fn swap_requires_ensures<T>(a: &mut T, b: &mut T)
            ensures *a == *old(b), *b == *old(a),
        {
            std::mem::swap(a, b)
        }
    } => Err(err) => assert_vir_error_msg(err, "duplicate specification for `core::mem::swap`")
}

// Test sane error message if you call a proxy

test_verify_one_file! {
    #[test] test_call_proxy verus_code! {
        #[verifier(external)]
        fn negate_bool(b: bool, x: u8) -> bool {
            !b
        }

        #[verifier(external_fn_specification)]
        fn negate_bool_requires_ensures(b: bool, x: u8) -> (ret_b: bool)
            requires x != 0,
            ensures ret_b == !b
        {
            negate_bool(b, x)
        }

        fn test() {
            negate_bool_requires_ensures(false, 1);
        }
    } => Err(err) => assert_vir_error_msg(err, "cannot call function `crate::negate_bool_requires_ensures` which is an artificial function for `assume_specification`; call `crate::negate_bool` instead")
}

test_verify_one_file! {
    #[test] test_call_external verus_code! {
        #[verifier(external)]
        fn some_external_fn() { }

        fn test() {
            some_external_fn();
        }
    } => Err(err) => assert_vir_error_msg(err, "cannot use function `crate::some_external_fn` which is ignored")
}

test_verify_one_file! {
    #[test] test_call_extern_external verus_code! {
        extern "C" {
            #[verifier(external)]
            fn stuff();
        }

        fn test() {
            stuff();
        }
    } => Err(err) => assert_vir_error_msg(err, "cannot use function `crate::stuff` which is ignored")
}

// If you wrongly try to apply a mode

test_verify_one_file! {
    #[test] test_proxy_marked_spec verus_code! {
        #[verifier(external)]
        fn negate_bool(b: bool, x: u8) -> bool {
            !b
        }

        #[verifier(external_fn_specification)]
        spec fn negate_bool_requires_ensures(b: bool, x: u8) -> bool
        {
            negate_bool(b, x)
        }
    } => Err(err) => assert_vir_error_msg(err, "an `assume_specification` declaration cannot be marked `spec`")
}

test_verify_one_file! {
    #[test] test_proxy_marked_proof verus_code! {
        #[verifier(external)]
        fn negate_bool(b: bool, x: u8) -> bool {
            !b
        }

        #[verifier(external_fn_specification)]
        proof fn negate_bool_requires_ensures(b: bool, x: u8) -> bool
        {
            negate_bool(b, x)
        }
    } => Err(err) => assert_vir_error_msg(err, "an `assume_specification` declaration cannot be marked `proof`")
}

// test visibility stuff

test_verify_one_file! {
    #[test] test_refers_to_closed_fn verus_code! {
        mod X {
            pub closed spec fn foo(b: bool, x: u8) -> bool {
                b && x == 0
            }

            #[verifier(external_fn_specification)]
            pub fn negate_bool_requires_ensures(b: bool, x: u8) -> bool
                requires foo(b, x)
            {
                crate::negate_bool(b, x)
            }
        }

        #[verifier(external)]
        pub fn negate_bool(b: bool, x: u8) -> bool {
            !b
        }

        pub fn test() {
            // this should fail because foo is closed
            negate_bool(true, 0); // FAILS
        }
    } => Err(err) => assert_fails(err, 1)
}

test_verify_one_file! {
    #[test] test_refers_to_open_fn verus_code! {
        mod X {
            pub open spec fn foo(b: bool, x: u8) -> bool {
                b && x == 0
            }

            #[verifier(external_fn_specification)]
            pub fn negate_bool_requires_ensures(b: bool, x: u8) -> bool
                requires foo(b, x)
            {
                crate::negate_bool(b, x)
            }
        }

        #[verifier(external)]
        pub fn negate_bool(b: bool, x: u8) -> bool {
            !b
        }

        pub fn test() {
            negate_bool(true, 0);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_refers_to_private_fn verus_code! {
        mod X {
            fn foo(b: bool, x: u8) -> bool {
                b && x == 0
            }

            #[verifier(external_fn_specification)]
            pub fn negate_bool_requires_ensures(b: bool, x: u8) -> bool
                requires foo(b, x)
            {
                negate_bool(b, x)
            }

            #[verifier(external)]
            pub fn negate_bool(b: bool, x: u8) -> bool {
                !b
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "in 'requires' clause of public function, cannot refer to private function")
}

test_verify_one_file! {
    #[test] test_proxy_is_more_private verus_code! {
        #[verifier(external_fn_specification)]
        fn negate_bool_requires_ensures(b: bool, x: u8) -> bool
        {
            negate_bool(b, x)
        }

        #[verifier(external)]
        pub fn negate_bool(b: bool, x: u8) -> bool {
            !b
        }
    } => Err(err) => assert_vir_error_msg(err, "an `assume_specification` declaration must be at least as visible as the function it provides a spec for")
}

test_verify_one_file! {
    #[test] test_proxy_is_more_private2 verus_code! {
        #[verifier(external_fn_specification)]
        fn swap_requires_ensures<T>(a: &mut T, b: &mut T)
            ensures *a == *old(b), *b == *old(a),
        {
            std::mem::swap(a, b)
        }
    } => Err(err) => assert_vir_error_msg(err, "an `assume_specification` declaration must be at least as visible as the function it provides a spec for")
}

// Test the attribute in weird places

test_verify_one_file! {
    #[test] test_attr_on_const verus_code! {
        #[verifier(external_fn_specification)]
        const x: u8 = 5;
    } => Err(err) => assert_vir_error_msg(err, "`assume_specification` attribute not supported for const")
}

test_verify_one_file! {
    #[test] test_attr_on_struct verus_code! {
        #[verifier(external_fn_specification)]
        struct X { }
    } => Err(err) => assert_vir_error_msg(err, "`external_fn_specification` attribute not supported here")
}

test_verify_one_file! {
    #[test] test_attr_on_impl verus_code! {
        struct X { }

        #[verifier(external_fn_specification)]
        impl X { }
    } => Err(err) => assert_vir_error_msg(err, "`external_fn_specification` attribute not supported here")
}

test_verify_one_file! {
    #[test] test_attr_on_trait verus_code! {
        #[verifier(external_fn_specification)]
        trait Tr { }
    } => Err(err) => assert_vir_error_msg(err, "`external_fn_specification` attribute not supported here")
}

test_verify_one_file! {
    #[test] test_attr_on_trait_fn verus_code! {
        trait Tr {
            #[verifier(external_fn_specification)]
            fn foo();
        }
    } => Err(err) => assert_vir_error_msg(err, "`assume_specification` declaration not supported here")
}

test_verify_one_file! {
    #[test] test_attr_on_trait_fn_impl verus_code! {
        trait Tr {
            fn foo();
        }

        struct X { }

        impl Tr for X {
            #[verifier(external_fn_specification)]
            fn foo() { }
        }
    } => Err(err) => assert_vir_error_msg(err, "`assume_specification` declaration not supported here")
}

test_verify_one_file! {
    #[test] test_attr_on_member_function verus_code! {
        struct X { }

        impl X {
            #[verifier(external_fn_specification)]
            fn stuff(&self) { }
        }
    } => Err(err) => assert_vir_error_msg(err, "`assume_specification` declaration not supported here")
}

test_verify_one_file! {
    #[test] test_attr_on_assoc_function verus_code! {
        struct X { }

        impl X {
            #[verifier(external_fn_specification)]
            fn stuff() { }
        }
    } => Err(err) => assert_vir_error_msg(err, "`assume_specification` declaration not supported here")
}

test_verify_one_file! {
    #[test] test_attr_on_foreign_function verus_code! {
        extern "C" {
            #[verifier(external_fn_specification)]
            fn stuff();
        }
    } => Err(err) => assert_vir_error_msg(err, "assume_specification not supported here")
}

// Mismatched type signatures

test_verify_one_file! {
    #[test] mismatch_params verus_code! {
        #[verifier(external)]
        fn x(b: bool) -> bool {
            b
        }

        #[verifier(external_fn_specification)]
        fn y(b: bool, c: bool) -> (ret_b: bool)
        {
            x(b)
        }
    } => Err(err) => assert_vir_error_msg(err, "assume_specification requires function type signature to match")
}

test_verify_one_file! {
    #[test] mismatch_params2 verus_code! {
        #[verifier(external)]
        fn x(b: bool) -> bool {
            b
        }

        #[verifier(external_fn_specification)]
        fn y(b: u8) -> (ret_b: bool)
        {
            x(false)
        }
    } => Err(err) => assert_vir_error_msg(err, "assume_specification requires function type signature to match")
}

test_verify_one_file! {
    #[test] mismatch_return verus_code! {
        #[verifier(external)]
        fn x<'a>(b: &'a mut bool) -> &'a mut bool {
            b
        }

        #[verifier(external_fn_specification)]
        fn y<'a>(b: &'a mut bool) -> (ret_b: &'a bool)
        {
            x(b)
        }
    } => Err(err) => assert_vir_error_msg(err, "assume_specification requires function type signature to match")
}

test_verify_one_file! {
    #[test] mismatch_type_params verus_code! {
        #[verifier(external)]
        fn x<S, T>(s: S, t: T) {
        }

        #[verifier(external_fn_specification)]
        fn y<S, T>(s: T, t: S)
        {
            x(t, s)
        }
    } => Err(err) => assert_vir_error_msg(err, "assume_specification requires function type signature to match")
}

test_verify_one_file! {
    #[test] mismatch_lt_params verus_code! {
        #[verifier(external)]
        fn x<'a, 'b>(u: &'a u8, v: &'b u8) -> &'a u8 {
            u
        }

        #[verifier(external_fn_specification)]
        fn y<'a, 'b>(u: &'b u8, v: &'a u8) -> &'a u8 {
            x(v, u)
        }
    } => Err(err) => assert_vir_error_msg(err, "assume_specification requires function type signature to match")
}

test_verify_one_file! {
    #[test] mismatch_extra_trait_bound verus_code! {
        #[verifier(external_fn_specification)]
        pub fn swap_requires_ensures<T: Copy>(a: &mut T, b: &mut T)
        {
            core::mem::swap(a, b)
        }
    } => Err(err) => assert_vir_error_msg(err, "assume_specification trait bound mismatch")
}

test_verify_one_file! {
    #[test] mismatch_extra_trait_bound2 verus_code! {
        #[verifier(external)]
        fn sw<T>(a: &mut T, b: &mut T) {
        }

        #[verifier(external_fn_specification)]
        fn swap_requires_ensures<T: Copy>(a: &mut T, b: &mut T)
        {
            sw(a, b)
        }
    } => Err(err) => assert_vir_error_msg(err, "assume_specification trait bound mismatch")
}

test_verify_one_file! {
    #[test] mismatch_trait_bound verus_code! {
        trait Tr1 { }
        trait Tr2 { }

        struct Stuff { }
        impl Tr1 for Stuff { }

        #[verifier(external)]
        fn x<T: Tr1>() {
        }

        #[verifier(external_fn_specification)]
        fn y<T: Tr2>()
        {
            x::<Stuff>()
        }
    } => Err(err) => assert_vir_error_msg(err, "assume_specification trait bound mismatch")
}

test_verify_one_file! {
    #[test] correct_trait_bound verus_code! {
        trait Tr1 { }

        struct Stuff { }
        impl Tr1 for Stuff { }

        #[verifier(external)]
        fn x<T: Tr1>() {
        }

        #[verifier(external_fn_specification)]
        fn y<T: Tr1>()
        {
            x::<Stuff>()
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] correct_trait_bound_renamed verus_code! {
        trait Tr1 { }

        struct Stuff { }
        impl Tr1 for Stuff { }

        #[verifier(external)]
        fn x<T: Tr1>() {
        }

        #[verifier(external_fn_specification)]
        fn y<S: Tr1>()
        {
            x::<S>()
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] mismatch_trait_bound2 verus_code! {
        trait Tr1 { }

        #[verifier(external)]
        fn f1<S, T: Tr1>(x: S, y: T) {
        }

        #[verifier(external_fn_specification)]
        fn f2<T: Tr1, S>(x: T, y: S)
        {
            f1(y, x)
        }
    } => Err(err) => assert_vir_error_msg(err, "assume_specification trait bound mismatch")
}

test_verify_one_file! {
    #[test] mismatch_trait_bound3 verus_code! {
        trait Tr1 { }

        #[verifier(external)]
        fn f1<S, T: Tr1>() {
        }

        #[verifier(external_fn_specification)]
        fn f2<T: Tr1, S>()
        {
            f1::<S, T>()
        }
    } => Err(err) => assert_vir_error_msg(err, "assume_specification trait bound mismatch")
}

// Lifetime checking

test_verify_one_file! {
    #[test] checking_lifetime verus_code! {
        use vstd::*;
        fn main(x: u8) {
            let mut a = x;
            core::mem::swap(&mut a, &mut a);
        }
    } => Err(err) => assert_rust_error_msg(err, "cannot borrow `a` as mutable more than once at a time")
}

test_verify_one_file! {
    #[test] checking_lifetime2 verus_code! {
        #[verifier(external)]
        fn foo<'a>(b: &'a bool) -> &'a bool {
            b
        }

        #[verifier(external_fn_specification)]
        fn foo_requires_ensures<'a>(b: &'a bool) -> &'a bool
        {
            foo(b)
        }

        fn test() {
            let mut x: bool = true;
            let y = foo(&x);
            x = false;
            foo(y);
        }
    } => Err(err) => assert_rust_error_msg(err, "cannot assign to `x` because it is borrowed")
}

// Check that you can't apply it to a trait function

test_verify_one_file! {
    #[test] apply_to_trait_fn_not_supported2 verus_code! {
        trait Tr { fn f(); }

        #[verifier(external_fn_specification)]
        fn ex_f<T: Tr>() {
            T::f()
        }
    } => Err(err) => assert_vir_error_msg(err, "assume_specification cannot be used to specify generic specifications of trait methods; consider using external_trait_specification instead")
}

// Other

test_verify_one_file! {
    #[test] test_attr_with_external verus_code! {
        #[verifier(external_fn_specification)]
        #[verifier(external)]
        pub fn swap_requires_ensures<T>(a: &mut T, b: &mut T)
            ensures *a == *old(b), *b == *old(a),
        {
            std::mem::swap(a, b)
        }
    } => Err(err) => assert_vir_error_msg(err, "an `assume_specification` declaration cannot be marked `external`")
}

test_verify_one_file! {
    #[test] test_attr_with_external_body verus_code! {
        #[verifier(external_fn_specification)]
        #[verifier(external_body)]
        pub fn swap_requires_ensures<T>(a: &mut T, b: &mut T)
            ensures *a == *old(b), *b == *old(a),
        {
            std::mem::swap(a, b)
        }
    } => Err(err) => assert_vir_error_msg(err, "an `assume_specification` declaration cannot be marked `external_body`")
}

test_verify_one_file! {
    #[test] test_attr_with_builtin verus_code! {
        #[verifier(external_fn_specification)]
        pub fn x() {
            admit()
        }
    } => Err(err) => assert_vir_error_msg(err, "cannot apply `assume_specification` to Verus builtin functions")
}

// Associated functions

test_verify_one_file! {
    #[test] assoc_function verus_code! {
        struct X { a: u8 }

        impl X {
            #[verifier::external]
            fn new(a: u8) -> Self {
                X { a: a }
            }
        }

        #[verifier::external_fn_specification]
        fn ex_X(a: u8) -> (res: X)
            ensures res.a == a,
        {
            X::new(a)
        }

        fn test() {
            let x = X::new(5);
            assert(x.a == 5);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] assoc_function_traits verus_code! {
        trait Tr1 { }
        trait Tr2 { }

        struct X<T> { a: T }

        impl<T: Tr2> X<T> {
            #[verifier::external]
            fn new(a: T) -> Self
                where T: Tr1
            {
                X { a: a }
            }
        }

        #[verifier::external_fn_specification]
        fn ex_X_new<T: Tr1 + Tr2>(a: T) -> (res: X<T>)
            ensures res.a == a,
        {
            X::<T>::new(a)
        }

        struct Foo(u8);
        impl Tr1 for Foo { }
        impl Tr2 for Foo { }

        fn test() {
            let x = X::<Foo>::new(Foo(5));
            assert(x.a == Foo(5));
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] assoc_function_traits_fail verus_code! {
        trait Tr1 { }
        trait Tr2 { }

        struct X<T> { a: T }

        impl<T> X<T> {
            #[verifier::external]
            fn new(a: T) -> Self
                where T: Tr1
            {
                X { a: a }
            }
        }

        #[verifier::external_fn_specification]
        fn ex_X_new<T: Tr1 + Tr2>(a: T) -> (res: X<T>)
            ensures res.a == a,
        {
            X::<T>::new(a)
        }
    } => Err(err) => assert_vir_error_msg(err, "assume_specification trait bound mismatch")
}

// Methods

test_verify_one_file! {
    #[test] method verus_code! {
        struct X { a: u8, b: u8 }

        impl X {
            #[verifier::external]
            fn swap(&self) -> X
            {
                X { a: self.b, b: self.a }
            }
        }

        #[verifier::external_fn_specification]
        fn ex_X_swap(x: &X) -> (res: X)
              ensures res.a == x.b && res.b == x.a
        {
            x.swap()
        }

        fn test() {
            let z = X { a: 5, b: 7 };
            let w = z.swap();

            assert(w == X { a: 7, b: 5 });
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] method_traits verus_code! {
        trait Tr1 { }
        trait Tr2 { }

        struct X<T> { a: T, b: T }

        impl<T: Tr2> X<T> {
            #[verifier::external]
            fn swap(self) -> X<T>
                where T: Tr1
            {
                X { a: self.b, b: self.a }
            }
        }

        #[verifier::external_fn_specification]
        fn ex_X_swap<T: Tr1 + Tr2>(x: X<T>) -> (res: X<T>)
              ensures res.a == x.b && res.b == x.a
        {
            x.swap()
        }

        struct Foo(u8);
        impl Tr1 for Foo { }
        impl Tr2 for Foo { }

        fn test() {
            let z = X::<Foo> { a: Foo(5), b: Foo(7) };
            let w = z.swap();

            assert(w == X { a: Foo(7), b: Foo(5) });
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] method_traits_fail verus_code! {
        trait Tr1 { }
        trait Tr2 { }

        struct X<T> { a: T, b: T }

        impl<T: Tr2> X<T> {
            #[verifier::external]
            fn swap(self) -> X<T>
            {
                X { a: self.b, b: self.a }
            }
        }

        #[verifier::external_fn_specification]
        fn ex_X_swap<T: Tr1 + Tr2>(x: X<T>) -> (res: X<T>)
              ensures res.a == x.b && res.b == x.a
        {
            x.swap()
        }
    } => Err(err) => assert_vir_error_msg(err, "assume_specification trait bound mismatch")
}

// allow_in_spec

test_verify_one_file! {
    #[test] test_allow_in_spec verus_code! {
        #[verifier::external]
        fn foo(x: bool) -> bool { !x }

        #[verifier::allow_in_spec]
        #[verifier::external_fn_specification]
        fn exec_foo(x: bool) -> (res: bool)
            returns !x
        {
            foo(x)
        }

        proof fn test() {
            let a = foo(true);
            assert(a == false);
        }

        fn test2() {
            let a = foo(true);
            assert(a == false);
        }

        fn test3() {
            let a = foo(true);
            assert(a == true); // FAILS
        }
    } => Err(err) => assert_fails(err, 1)
}

// when_used_as_spec

test_verify_one_file! {
    #[test] test_when_used_as_spec verus_code! {
        #[verifier::external]
        fn foo(x: bool) -> bool { !x }

        spec fn spec_not(x: bool) -> bool { !x }

        #[verifier::when_used_as_spec(spec_not)]
        #[verifier::external_fn_specification]
        fn exec_foo(x: bool) -> (res: bool)
        {
            foo(x)
        }

        proof fn test() {
            let a = foo(true);
            assert(a == false);
        }

        fn test2() {
            let a = foo(true);
            assert(a == false); // FAILS
        }
    } => Err(err) => assert_fails(err, 1)
}

test_verify_one_file! {
    #[test] test_when_used_as_spec_modules verus_code! {
        mod ExternalMod {
            #[verifier::external]
            pub fn foo(x: bool) -> bool { !x }
        }

        mod OtherMod {
            use super::ExternalMod;

            pub open spec fn spec_not(x: bool) -> bool { !x }

            #[verifier::when_used_as_spec(spec_not)]
            #[verifier::external_fn_specification]
            pub fn exec_foo(x: bool) -> (res: bool)
            {
                ExternalMod::foo(x)
            }

            pub proof fn test() {
                let a = ExternalMod::foo(true);
                assert(a == false);
            }

            pub fn test2() {
                let a = ExternalMod::foo(true);
                assert(a == false); // FAILS
            }
        }
    } => Err(err) => assert_fails(err, 1)
}

test_verify_one_file! {
    #[test] test_when_used_as_spec_call_proxy verus_code! {
        #[verifier::external]
        fn foo(x: bool) -> bool { !x }

        spec fn spec_not(x: bool) -> bool { !x }

        #[verifier::when_used_as_spec(spec_not)]
        #[verifier::external_fn_specification]
        fn exec_foo(x: bool) -> (res: bool)
        {
            foo(x)
        }

        proof fn test() {
            let a = exec_foo(true);
            assert(a == false);
        }
    } => Err(err) => assert_vir_error_msg(err, "cannot call function `crate::exec_foo` which is an artificial function for `assume_specification`; call `crate::foo` instead")
}

test_verify_one_file! {
    #[test] when_used_as_spec_attribute_refers_to_proxy verus_code! {
        #[verifier::external]
        fn foo(x: bool) -> bool { !x }

        #[verifier::external_fn_specification]
        fn exec_foo(x: bool) -> (res: bool)
        {
            foo(x)
        }

        #[verifier::when_used_as_spec(exec_foo)]
        fn test(x: bool) -> (res: bool)
        {
            !x
        }
    } => Err(err) => assert_vir_error_msg(err, "cannot find function referred to in when_used_as_spec")
}

test_verify_one_file! {
    #[test] when_used_as_spec_more_private verus_code! {
        spec fn stuff() {
        }

        #[verifier::when_used_as_spec(stuff)]
        pub fn ex_likely(x: bool) -> (res: bool)
            ensures res == x
        {
            std::intrinsics::likely(x)
        }
    } => Err(err) => assert_vir_error_msg(err, "when_used_as_spec refers to function which is more private")
}

// Specifying impls of foreign traits

test_verify_one_file! {
    #[test] foregin_trait1 verus_code! {
        #[verifier(external_fn_specification)]
        pub fn ex_u8_default() -> (res: u8)
            ensures res == 0
        {
            u8::default()
        }

        fn test() {
            let x = u8::default();
            assert(x == 0);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] foreign_trait3 verus_code! {
        #[verifier::external]
        trait Tr {
            fn f(t: u8);
        }

        impl Tr for X {
            fn f(t: u8) { }
        }

        struct X { }

        #[verifier(external_fn_specification)]
        pub fn ex_f_default(t: u8)
            requires t == 5,
        {
            X::f(t)
        }
    } => Err(err) => assert_vir_error_msg(err, "duplicate specification for `crate::X::f`")
}

test_verify_one_file! {
    #[test] foreign_trait5 verus_code! {
        #[verifier::external]
        trait Tr {
            fn f(t: u8);
        }

        #[verifier::external]
        impl Tr for X {
            fn f(t: u8) { }
        }

        struct X { }

        #[verifier(external_fn_specification)]
        pub fn ex_f_default(t: u8)
            requires t == 5,
        {
            X::f(t)
        }

        fn test() {
            X::f(5);
        }

        fn test2() {
            X::f(6); // FAILS
        }
    } => Err(err) => assert_fails(err, 1)
}

test_verify_one_file! {
    #[test] foreign_trait6 verus_code! {
        pub enum Foo<T> {
            One(T),
            Two,
        }

        #[verifier::external]
        impl<T> Default for Foo<T> {
            fn default() -> Foo<T> {
                Foo::Two
            }
        }

        #[verifier(external_fn_specification)]
        pub fn ex_foo_default<T>() -> (res: Foo<T>)
            ensures res == Foo::<T>::Two
        {
            Foo::<T>::default()
        }

        fn test() {
            let x = Foo::<u8>::default();
            assert(x == Foo::<u8>::Two);
        }

        fn test2<T>() {
            let x = Foo::<T>::default();
            assert(x == Foo::<T>::Two);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] foreign_trait7 verus_code! {
        pub enum Foo<T, U> {
            One(T),
            Two,
            Three(U),
        }

        #[verifier::external]
        impl<T, U> Default for Foo<T, U> {
            fn default() -> Foo<T, U> {
                Foo::Two
            }
        }

        #[verifier(external_fn_specification)]
        pub fn ex_foo_default<T, U>() -> (res: Foo<T, U>)
            ensures res == Foo::<T, U>::Two
        {
            Foo::<T, U>::default()
        }

        fn test<T>() {
            let x = Foo::<T, u8>::default();
            assert(x == Foo::<T, u8>::Two);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] foreign_trait_use_self_1 verus_code! {
        #[verifier::external]
        trait Tr {
            fn f(&self) -> bool;
        }

        #[verifier::external]
        impl Tr for X {
            fn f(&self) -> bool { true }
        }

        pub struct X { a: u8 }

        #[verifier(external_fn_specification)]
        pub fn ex_x_f(x: &X) -> bool
            requires x.a == 5,
        {
            x.f()
        }

        fn test() {
            let x = X { a: 5 };
            let b = x.f();
        }

        fn test2() {
            let x = X { a: 6 };
            let b = x.f(); // FAILS
        }
    } => Err(err) => assert_fails(err, 1)
}

// I think the reason this test doesn't work is because Ord has a default
// implementation of 'max', which 'u8' uses. Thus our attempts to statically resolve
// the trait function don't work.

test_verify_one_file! {
    #[ignore] #[test] foreign_trait_use_self_2 verus_code! {
        #[verifier(external_fn_specification)]
        pub fn ex_u8_max(a: u8, b: u8) -> (res: u8)
            ensures res == if a > b { a } else { b },
        {
            a.max(b)
        }

        fn test() {
            let a: u8 = 5;
            let b: u8 = 12;
            let x = a.max(b);
            assert(x == 12);
        }
    } => Err(err) => assert_fails(err, 1)
}

test_verify_one_file! {
    #[test] foreign_trait_use_self_3 verus_code! {
        use std::ops::Not;

        #[verifier(external_fn_specification)]
        pub fn ex_u8_not(a: u8) -> (res: u8)
            ensures res == !a
        {
            a.not()
        }

        fn test() {
            let a: u8 = 5;
            let x = a.not();
            assert(x == !5u8);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] foreign_trait_with_autospec verus_code! {
        use std::ops::Not;

        pub open spec fn wrong_not(a: u8) -> u8 { (255 - a) as u8 }

        #[verifier(external_fn_specification)]
        #[verifier::when_used_as_spec(wrong_not)]
        pub fn ex_u8_not(a: u8) -> (res: u8)
            ensures res == !a
        {
            a.not()
        }

        fn test() {
            let a: u8 = 5;
            let x = a.not();
            assert(x == !5u8);
        }

        proof fn test2() {
            let a: u8 = 5;
            let x = a.not();
            assert(x == 250);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_foreign_trait_and_trait_bound verus_code! {
        struct Ve<A, B> { a: A, b: B }
        struct Gl { }

        #[verifier::external]
        trait Al { }

        impl Al for Gl { }

        #[verifier::external]
        pub trait SomeTr<T> {
            fn gget(&self, i: usize) -> &T;
            fn set(&mut self, i: usize, value: T);
            fn set_and_swap(&mut self, i: usize, value: &mut T);
        }

        impl<T, A: Al> SomeTr<T> for Ve<T, A> {
            #[verifier::external_body]
            fn gget(&self, i: usize) -> (element: &T)
                requires i == 0
            {
                unimplemented!();
            }

            #[verifier::external_body]
            fn set(&mut self, i: usize, value: T)
            {
                unimplemented!();
            }

            #[verifier::external_body]
            fn set_and_swap(&mut self, i: usize, value: &mut T)
            {
                unimplemented!();
            }
        }

        fn test<T>(v: Ve<T, Gl>) {
            let x = v.gget(0);
        }

        fn test2<T>(v: Ve<T, Gl>) {
            let x = v.gget(1); // FAILS
        }
    } => Err(err) => assert_fails(err, 1)
}

test_verify_one_file! {
    #[test] test_trait_method_impl_is_external_error verus_code! {
        pub struct X { t: u8 }

        trait Tr {
            fn foo(&self);
        }

        pub fn stuff(x: X) {
            x.foo();
        }


        #[verifier::external]
        impl Tr for X {
            fn foo(&self) { }
        }
    } => Err(err) => assert_vir_error_msg(err, "cannot use function `crate::X::foo` which is ignored")
}

test_verify_one_file! {
    #[ignore] #[test] external_trait_item_error verus_code! {
        trait Tr {
            #[verifier::external]
            fn foo(&self);
        }
    } => Err(err) => assert_vir_error_msg(err, "a trait item cannot be marked 'external'")
}

test_verify_one_file! {
    #[ignore] #[test] external_trait_impl_item_error verus_code! {
        trait Tr {
            fn foo(&self);
        }

        pub struct X { t: u8 }

        impl Tr for X {
            #[verifier::external]
            fn foo(&self) { }
        }
    } => Err(err) => assert_vir_error_msg(err, "an item in a trait impl cannot be marked 'external'")
}

test_verify_one_file! {
    #[test] test_returns_clause verus_code! {
        #[verifier(external)]
        fn negate_bool(b: bool, x: u8) -> bool {
            !b
        }

        #[verifier(external_fn_specification)]
        fn negate_bool_requires_ensures(b: bool, x: u8) -> bool
            requires x != 0,
            returns !b
        {
            negate_bool(b, x)
        }

        fn test1() {
            let ret_b = negate_bool(true, 1);
            assert(ret_b == false);
        }

        fn test2() {
            let ret_b = negate_bool(true, 0); // FAILS
        }

        fn test3() {
            let ret_b = negate_bool(true, 1);
            assert(ret_b == true); // FAILS
        }
    } => Err(err) => assert_fails(err, 2)
}

test_verify_one_file! {
    #[test] provided_trait_method verus_code! {
        pub trait Tr {
            fn foo(&self) -> bool { true }
        }

        pub struct X { }

        impl Tr for X {
        }

        verus!{
            #[verifier(external_type_specification)]
            pub struct ExX(X);

            #[verifier(external_fn_specification)]
            pub fn ex_X_foo(p: &X) -> bool {
                p.foo()
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "assume_specification for a provided trait method")
}

test_verify_one_file! {
    #[test] module_external code! {
        #[verifier::external]
        mod moo {
            #[verifier::verify]
            fn stuff() {
                builtin::assert_(false);
            }
        }
    } => Ok(err) => {
        assert!(err.warnings.len() == 2);
        assert!(err.warnings[0].message.contains("#[verifier::verify] has no effect because item is already marked external"));
    }
}

test_verify_one_file! {
    #[test] test_trait_with_assoc_type_bounds verus_code! {
        trait Sr {
            fn s_foo(&self);
        }

        trait Tr {
            type AssocType: Sr;

            fn t_foo(&self) -> Self::AssocType;
        }

        struct X { u: u64 }
        struct Y { }

        impl Sr for X {
            fn s_foo(&self) { }
        }

        #[verifier::external]
        impl Tr for Y {
            type AssocType = X;

            fn t_foo(&self) -> X {
                X { u: 0 }
            }
        }

        assume_specification [ Y::t_foo ] (y: &Y) -> (x: X)
            ensures x == (X { u: 0 });

        fn test(y: &Y) {
            let j = y.t_foo();
            assert(j == X { u: 0 });
        }

        fn test_fails(y: &Y) {
            let j = y.t_foo();
            assert(j == X { u: 0 });
            assert(false); // FAILS
        }
    } => Err(err) => assert_fails(err, 1)
}

test_verify_one_file! {
    #[test] test_blanket_impl_mismatch verus_code! {
        use std::fmt::Display;
        // This is missing the ?Sized bound:
        pub assume_specification<T: Display>[ T::to_string ](this: &T) -> (other: String);
    } => Err(err) => assert_vir_error_msg(err, "assume_specification trait bound mismatch")
}

test_verify_one_file! {
    #[test] test_blanket_impl verus_code! {
        trait Tr {
            fn stuff(&self)
                ensures self.foo();

            spec fn foo(&self) -> bool;
        }

        #[verifier::external]
        trait Blanket {
            fn stuff2(&self);
        }

        #[verifier::external]
        impl<T: Tr> Blanket for T {
            fn stuff2(&self) {
                self.stuff();
            }
        }

        assume_specification <T: Tr> [ <T as Blanket>::stuff2 ] (x: &T)
            ensures x.foo();


        fn test_generic<T: Tr>(t: &T) {
            t.stuff2();
            assert(t.foo());
        }

        impl Tr for u64 {
            fn stuff(&self) {
                assume(false);
            }

            spec fn foo(&self) -> bool {
                self < 5
            }
        }

        fn test_specific(u: u64) {
            u.stuff2();
            assert(u < 5);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_blanket_impl_unsized verus_code! {
        trait Tr {
            fn stuff(&self)
                ensures self.foo();

            spec fn foo(&self) -> bool;
        }

        #[verifier::external]
        trait Blanket {
            fn stuff2(&self);
        }

        #[verifier::external]
        impl<T: Tr + ?Sized> Blanket for T {
            fn stuff2(&self) {
                self.stuff();
            }
        }

        assume_specification <T: Tr + ?Sized> [ <T as Blanket>::stuff2 ] (x: &T)
            ensures x.foo();


        fn test_generic<T: Tr + ?Sized>(t: &T) {
            t.stuff2();
            assert(t.foo());
        }

        impl Tr for u64 {
            fn stuff(&self) {
                assume(false);
            }

            spec fn foo(&self) -> bool {
                self < 5
            }
        }

        fn test_specific(u: u64) {
            u.stuff2();
            assert(u < 5);
        }
    } => Ok(())
}

// `Deref` is special since it has an alias `*` for calling `.deref()`.

test_verify_one_file! {
    #[test] test_manually_drop_deref_when_have_spec verus_code! {
        use core::mem::ManuallyDrop;
        use core::ops::Deref;

        #[verifier::external_type_specification]
        #[verifier::external_body]
        #[verifier::reject_recursive_types(T)]
        pub struct ExManuallyDrop<T: ?Sized>(ManuallyDrop<T>);

        pub uninterp spec fn manually_drop_spec_get<T: ?Sized>(m: &ManuallyDrop<T>) -> &T;

        #[verifier::when_used_as_spec(manually_drop_spec_get)]
        pub assume_specification<T: ?Sized >[ <ManuallyDrop<T> as Deref>::deref ](
            v: &ManuallyDrop<T>,
        ) -> (res: &T)
            ensures
                res == manually_drop_spec_get(v),
        ;

        fn do_exec_deref(x: &ManuallyDrop<usize>)
            requires 100 <= **x < 102
        {
            // Explicit call.
            let u: &usize = &((*x).deref());
            assert(100 <= *u < 102);
            // Implicit call.
            let v: &usize = &**x;
            assert(100 <= *v < 102);
        }

        spec fn do_explicit_spec_deref(x: &ManuallyDrop<usize>) -> &usize {
            &((*x).deref())
        }

        spec fn do_implicit_spec_deref(x: &ManuallyDrop<usize>) -> &usize {
            &**x
        }
    } => Ok(())
}

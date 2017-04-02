package com.robertchrzanowski.zitchia

import org.junit.Assert.assertEquals
import org.junit.Assert.assertNotEquals
import org.junit.FixMethodOrder
import org.junit.Test
import org.junit.runners.MethodSorters
import java.util.Random

@FixMethodOrder(MethodSorters.NAME_ASCENDING)
class ExampleUnitTest {

    @Test
    @Throws(Exception::class)
    fun t00_equality(): Unit {

        val positiveCases = mapOf(
            Symbol("foo") to Symbol("foo"),
            Symbol("bar") to Symbol("bar"),
            TruePrimitive to TruePrimitive,
            FalsePrimative to FalsePrimative,
            Undefined to Undefined,
            Primitive(1.0) to Primitive(1.0),
            Primitive(2.0) to Primitive(2.0),
            Nil to Nil,
            Cons(Symbol("a"), Cons(Symbol("b"), Cons(Symbol("c"), Nil))) to
                Cons(Symbol("a"), Cons(Symbol("b"), Cons(Symbol("c"), Nil))),
            Cons(Primitive(1.0), Cons(Primitive(2.0), Cons(Primitive(3.0), Nil))) to
                Cons(Primitive(1.0), Cons(Primitive(2.0), Cons(Primitive(3.0), Nil))),
            Cons(Primitive(1.0), Cons(Cons(Primitive(2.0), Cons(Cons(Primitive(3.0), Nil), Nil)), Nil)) to
                Cons(Primitive(1.0), Cons(Cons(Primitive(2.0), Cons(Cons(Primitive(3.0), Nil), Nil)), Nil)))

        val negativeCases = mapOf(
            Symbol("bar") to Symbol("foo"),
            Symbol("foo") to Symbol("bar"),
            FalsePrimative to TruePrimitive,
            TruePrimitive to FalsePrimative,
            Symbol("foo") to Undefined,
            Undefined to Symbol("foo"),
            Primitive(2.0) to Primitive(1.0),
            Primitive(1.0) to Primitive(2.0),
            Cons(Primitive(1.0), Cons(Primitive(2.0), Cons(Primitive(3.0), Nil))) to
                Cons(Symbol("a"), Cons(Symbol("b"), Cons(Symbol("c"), Nil))),
            Cons(Symbol("a"), Cons(Symbol("b"), Cons(Symbol("c"), Nil))) to
                Cons(Primitive(1.0), Cons(Primitive(2.0), Cons(Primitive(3.0), Nil))))

        for ((expected, actual) in positiveCases) {
            assertEquals("$expected === $actual: ", expected, actual)
        }

        for ((expected, actual) in negativeCases) {
            assertNotEquals("$expected === $actual: ", expected, actual)
        }
    }

    @Test
    @Throws(Exception::class)
    fun t01_addition(): Unit {
        val r = Random()

        for (unused in 1..10) {
            val x = r.nextDouble()
            val y = r.nextDouble()

            val expression = "(+ $x $y)"
            val expected = x + y
            val actualSeq = eval(read(tokenize(expression)))

            for (i in actualSeq) {
                val actual = ((i as? Primitive<*>)?.value as? Double)
                assertEquals("$expression === $actual: expected $expected", expected, actual)
            }
        }
    }

    @Test
    @Throws(Exception::class)
    fun t02_subtraction(): Unit {
        val r = Random()

        for (unused in 1..10) {
            val x = r.nextDouble()
            val y = r.nextDouble()

            val expression = "(- $x $y)"
            val expected = x - y
            val actualSeq = eval(read(tokenize(expression)))

            for (i in actualSeq) {
                val actual = ((i as? Primitive<*>)?.value as? Double)
                assertEquals("$expression === $actual: expected $expected", expected, actual)
            }
        }
    }

    @Test
    @Throws(Exception::class)
    fun t03_multiplication(): Unit {
        val r = Random()

        for (unused in 1..10) {
            val x = r.nextDouble()
            val y = r.nextDouble()

            val expression = "(* $x $y)"
            val expected = x * y
            val actualSeq = eval(read(tokenize(expression)))

            for (i in actualSeq) {
                val actual = ((i as? Primitive<*>)?.value as? Double)
                assertEquals("$expression === $actual: expected $expected", expected, actual)
            }
        }
    }

    @Test
    @Throws(Exception::class)
    fun t04_division(): Unit {
        val r = Random()

        for (unused in 1..10) {
            val x = r.nextDouble()
            val y = r.nextDouble()

            val expression = "(/ $x $y)"
            val expected = x / y
            val actualSeq = eval(read(tokenize(expression)))

            for (i in actualSeq) {
                val actual = ((i as? Primitive<*>)?.value as? Double)
                assertEquals("$expression === $actual: expected $expected", expected, actual)
            }
        }
    }

    @Test
    @Throws(Exception::class)
    fun t05_comparison(): Unit {

        val positiveCases = mapOf(
            "(< 1 2)" to TruePrimitive,
            "(< 2 1)" to FalsePrimative,
            "(> 1 2)" to FalsePrimative,
            "(> 2 1)" to TruePrimitive,
            "(<= 1 2)" to TruePrimitive,
            "(<= 2 1)" to FalsePrimative,
            "(>= 1 2)" to FalsePrimative,
            "(>= 2 1)" to TruePrimitive,
            "(<= 1 1)" to TruePrimitive,
            "(>= 1 1)" to TruePrimitive,
            "(< 1 2 3)" to TruePrimitive,
            "(< 3 2 1)" to FalsePrimative,
            "(> 1 2 3)" to FalsePrimative,
            "(> 3 2 1)" to TruePrimitive,
            "(<= 1 2 3)" to TruePrimitive,
            "(<= 3 2 1)" to FalsePrimative,
            "(>= 1 2 3)" to FalsePrimative,
            "(>= 3 2 1)" to TruePrimitive,
            "(<= 1 1 1)" to TruePrimitive,
            "(>= 1 1 1)" to TruePrimitive)

        for ((expression, expected) in positiveCases) {
            for (actual in eval(read(tokenize(expression)))) {
                assertEquals("$expression === $actual: expected $expected", expected, actual)
            }
        }
    }

    @Test
    @Throws(Exception::class)
    fun t06_quote(): Unit {
        val positiveCases = mapOf(
            "(quote foo)" to Symbol("foo"),
            "(quote bar)" to Symbol("bar"),
            "(quote true)" to TruePrimitive,
            "(quote false)" to FalsePrimative,
            "(quote undefined)" to Undefined,
            "(quote 1)" to Primitive(1.0),
            "(quote 2)" to Primitive(2.0),
            "(quote ())" to Nil,
            "(quote (a b c))" to Cons(Symbol("a"), Cons(Symbol("b"), Cons(Symbol("c"), Nil))),
            "(quote (1 2 3))" to Cons(Primitive(1.0), Cons(Primitive(2.0), Cons(Primitive(3.0), Nil))),
            "(quote (1 (2 (3))))" to Cons(Primitive(1.0), Cons(Cons(Primitive(2.0), Cons(Cons(Primitive(3.0), Nil), Nil)), Nil)),
            "'foo" to Symbol("foo"),
            "'bar" to Symbol("bar"),
            "'true" to TruePrimitive,
            "'false" to FalsePrimative,
            "'undefined" to Undefined,
            "'1" to Primitive(1.0),
            "'2" to Primitive(2.0),
            "'()" to Nil,
            "'(a b c)" to Cons(Symbol("a"), Cons(Symbol("b"), Cons(Symbol("c"), Nil))),
            "'(1 2 3)" to Cons(Primitive(1.0), Cons(Primitive(2.0), Cons(Primitive(3.0), Nil))),
            "'(1 (2 (3)))" to Cons(Primitive(1.0), Cons(Cons(Primitive(2.0), Cons(Cons(Primitive(3.0), Nil), Nil)), Nil)))

        for ((expression, expected) in positiveCases) {
            for (actual in eval(read(tokenize(expression)))) {
                assertEquals("$expression === $actual: expected $expected", expected, actual)
            }
        }
    }

    @Test
    @Throws(Exception::class)
    fun t07_quasiquote(): Unit {
        val positiveCases = mapOf(
            "(quasiquote foo)" to Symbol("foo"),
            "(quasiquote bar)" to Symbol("bar"),
            "(quasiquote true)" to TruePrimitive,
            "(quasiquote false)" to FalsePrimative,
            "(quasiquote undefined)" to Undefined,
            "(quasiquote 1)" to Primitive(1.0),
            "(quasiquote 2)" to Primitive(2.0),
            "(quasiquote ())" to Nil,
            "(quasiquote (a b c))" to Cons(Symbol("a"), Cons(Symbol("b"), Cons(Symbol("c"), Nil))),
            "(quasiquote (1 2 3))" to Cons(Primitive(1.0), Cons(Primitive(2.0), Cons(Primitive(3.0), Nil))),
            "(quasiquote (1 (2 (3))))" to Cons(Primitive(1.0), Cons(Cons(Primitive(2.0), Cons(Cons(Primitive(3.0), Nil), Nil)), Nil)),
            "(quasiquote (unquote true))" to TruePrimitive,
            "(quasiquote (unquote false))" to FalsePrimative,
            "(quasiquote (unquote undefined))" to Undefined,
            "(quasiquote (unquote 1))" to Primitive(1.0),
            "(quasiquote (unquote 2))" to Primitive(2.0),
            "(quasiquote (unquote ()))" to Nil,
            "(quasiquote (unquote (+ 1 2 3)))" to Primitive(6.0),
            "(quasiquote (foo (unquote (+ 1 2 3))))" to Cons(Symbol("foo"), Cons(Primitive(6.0), Nil)),

            "`foo" to Symbol("foo"),
            "`bar" to Symbol("bar"),
            "`true" to TruePrimitive,
            "`false" to FalsePrimative,
            "`undefined" to Undefined,
            "`1" to Primitive(1.0),
            "`2" to Primitive(2.0),
            "`()" to Nil,
            "`(a b c)" to Cons(Symbol("a"), Cons(Symbol("b"), Cons(Symbol("c"), Nil))),
            "`(1 2 3)" to Cons(Primitive(1.0), Cons(Primitive(2.0), Cons(Primitive(3.0), Nil))),
            "`(1 (2 (3)))" to Cons(Primitive(1.0), Cons(Cons(Primitive(2.0), Cons(Cons(Primitive(3.0), Nil), Nil)), Nil)),
            "`(unquote true)" to TruePrimitive,
            "`(unquote false)" to FalsePrimative,
            "`(unquote undefined)" to Undefined,
            "`(unquote 1)" to Primitive(1.0),
            "`(unquote 2)" to Primitive(2.0),
            "`(unquote ())" to Nil,
            "`(unquote (+ 1 2 3))" to Primitive(6.0),
            "`(foo (unquote (+ 1 2 3)))" to Cons(Symbol("foo"), Cons(Primitive(6.0), Nil)),

            "`,true" to TruePrimitive,
            "`,false" to FalsePrimative,
            "`,undefined" to Undefined,
            "`,1" to Primitive(1.0),
            "`,2" to Primitive(2.0),
            "`,()" to Nil,
            "`,(+ 1 2 3)" to Primitive(6.0),
            "`(foo ,(+ 1 2 3))" to Cons(Symbol("foo"), Cons(Primitive(6.0), Nil)))

        for ((expression, expected) in positiveCases) {
            for (actual in eval(read(tokenize(expression)))) {
                assertEquals("$expression === $actual: expected $expected", expected, actual)
            }
        }
    }

    @Test
    @Throws(Exception::class)
    fun t08_cons(): Unit {

        val positiveCases = mapOf(
            "(cons 'foo ())" to Cons(Symbol("foo"), Nil),
            "(cons 'foo (cons 'bar ()))" to Cons(Symbol("foo"), Cons(Symbol("bar"), Nil)))

        for ((expression, expected) in positiveCases) {
            for (actual in eval(read(tokenize(expression)))) {
                assertEquals("$expression === $actual: expected $expected", expected, actual)
            }
        }
    }

    @Test
    @Throws(Exception::class)
    fun t09_car(): Unit {

        val positiveCases = mapOf(
            "(car '(a b c))" to Symbol("a"),
            "(car '(1 2 3))" to Primitive(1.0),
            "(car '(true false))" to TruePrimitive)

        for ((expression, expected) in positiveCases) {
            for (actual in eval(read(tokenize(expression)))) {
                assertEquals("$expression === $actual: expected $expected", expected, actual)
            }
        }
    }

    @Test
    @Throws(Exception::class)
    fun t10_cdr(): Unit {

        val positiveCases = mapOf(
            "(cdr '(a b c))" to Cons(Symbol("b"), Cons(Symbol("c"), Nil)),
            "(cdr '(1 2 3))" to Cons(Primitive(2.0), Cons(Primitive(3.0), Nil)),
            "(cdr '(true false))" to Cons(FalsePrimative, Nil))

        for ((expression, expected) in positiveCases) {
            for (actual in eval(read(tokenize(expression)))) {
                assertEquals("$expression === $actual: expected $expected", expected, actual)
            }
        }
    }

    @Test
    @Throws(Exception::class)
    fun t11_if(): Unit {
        val expression0 = "(if true (quote foo) (quote bar))"
        val actualSeq0 = eval(read(tokenize(expression0)))

        for (i in actualSeq0) {
            val actual = (i as? Symbol)?.symbol
            assertEquals("foo", actual)
        }

        val expression1 = "(if false (quote foo) (quote bar))"
        val actualSeq1 = eval(read(tokenize(expression1)))

        for (i in actualSeq1) {
            val actual = (i as? Symbol)?.symbol
            assertEquals("bar", actual)
        }

        val expression2 = "(if undefined (quote foo) (quote bar))"
        val actualSeq2 = eval(read(tokenize(expression2)))

        for (i in actualSeq2) {
            val actual = (i as? Symbol)?.symbol
            assertEquals("bar", actual)
        }

        val expression3 = "(if (quote baz) (quote foo) (quote bar))"
        val actualSeq3 = eval(read(tokenize(expression3)))

        for (i in actualSeq3) {
            val actual = (i as? Symbol)?.symbol
            assertEquals("foo", actual)
        }

        // Should error

        val expression4 = "(if (quote baz) (quote foo) (quote bar) (quote bat))"
        val actualSeq4 = eval(read(tokenize(expression4)))

        for (i in actualSeq4) {
            val actual = (i as? Symbol)?.symbol
            assertEquals("foo", actual)
        }
    }

    @Test
    @Throws(Exception::class)
    fun t12_define(): Unit {

        val positiveCases = mapOf(
            "(define foo 'foo)" to Symbol("foo"),
            "foo" to Symbol("foo"),
            "(define bar 'bar)" to Symbol("bar"),
            "bar" to Symbol("bar"),
            "(define baz (+ 1 2))" to Primitive(3.0),
            "baz" to Primitive(3.0))

        for ((expression, expected) in positiveCases) {
            for (actual in eval(read(tokenize(expression)))) {
                assertEquals("$expression === $actual: expected $expected", expected, actual)
            }
        }
    }

    @Test
    @Throws(Exception::class)
    fun t13_lambda(): Unit {

        val positiveCases = mapOf(
            "((lambda () 0))" to Primitive(0.0),
            "((lambda (x) x) 1)" to Primitive(1.0),
            "((lambda (x) (* x x)) 2)" to Primitive(4.0),
            "((lambda (x y) x) 3 4)" to Primitive(3.0),
            "(((lambda (x) (lambda (y) x)) 5) 6)" to Primitive(5.0),
            "((lambda (... args) (car (cdr (cdr args)))) 1 2 3)" to Primitive(3.0),
            "((lambda (a ... args) (car args)) 1 2 3)" to Primitive(2.0),
            "((lambda (a b ... args) args) 1 2)" to Nil,
            "((lambda (a b c ... args) args) 1 2)" to Nil)

        for ((expression, expected) in positiveCases) {
            for (actual in eval(read(tokenize(expression)))) {
                assertEquals("$expression === $actual: expected $expected", expected, actual)
            }
        }
    }

    @Test
    @Throws(Exception::class)
    fun t14_recurse(): Unit {

        val positiveCases = mapOf(
            "((recurse fac (n) (if (<= n 1) n (* n (fac (- n 1))))) 4)" to Primitive(24.0),
            "((recurse fib (n) (if (< n 2) n (+ (fib (- n 1)) (fib (- n 2))))) 6)" to Primitive(8.0))

        for ((expression, expected) in positiveCases) {
            for (actual in eval(read(tokenize(expression)))) {
                assertEquals("$expression === $actual: expected $expected", expected, actual)
            }
        }
    }

    @Test
    @Throws(Exception::class)
    fun t15_macro(): Unit {

        val positiveCases = mapOf(
            "((macro (a) ~a) 1)" to Primitive(1.0),
            "((macro (a) a) 1)" to Undefined,
            "(and)" to TruePrimitive,
            "(and 'a)" to TruePrimitive,
            "(and 'a 'b undefined)" to Undefined,
            "(and 'a 'b ())" to Nil,
            "(and 'a 'b)" to TruePrimitive,
            "(or)" to FalsePrimative,
            "(or true)" to TruePrimitive,
            "(or false undefined () 'a)" to Symbol("a"),
            "(cond)" to Undefined,
            "(cond true 1)" to Primitive(1.0),
            "(cond false 2 true 1)" to Primitive(1.0),
            "(cond undefined 2 'a 1)" to Primitive(1.0),
            "(cond () 2 '(a) 1)" to Primitive(1.0))

        for ((expression, expected) in positiveCases) {
            val actual = eval(read(tokenize(expression))).lastOrNull()
            assertEquals("$expression == $actual: expected $expected", expected, actual)
        }
    }

    @Test
    @Throws(Exception::class)
    fun t16_extensions(): Unit {

        val positiveCases = mapOf(
            "(defun foo (x) x) (foo 1)" to Primitive(1.0),
            "(eval '1)" to Primitive(1.0),
            "(eval ``(1 ,(cons 2 ())))" to Cons(Primitive(1.0), Cons(Cons(Primitive(2.0), Nil), Nil)))

        for ((expression, expected) in positiveCases) {
            val actual = eval(read(tokenize(expression))).lastOrNull()
            assertEquals("$expression == $actual: expected $expected", expected, actual)
        }
    }

//    @Test
//    @Throws(Exception::class)
//    fun t16_patternMatching(): Unit {
//
//        val positiveCases = mapOf(
//                "((lambda '(0) 1" +
//                "         '(1) 1" +
//                "          (x) (+ (self (- x 1))" +
//                "                 (self (- x 2)))) 5)" to Expression.Atom.Primitive(8.0),
//                "((lambda (... args)" +
//                "         (match args" +
//                "                '(0) 1" +
//                "                '(1) 1" +
//                "                (x) (+ (self (- x 1))" +
//                "                       (self (- x 2))" to Expression.Atom.Primitive(8.0),
//
//
//        for ((expression, expected) in positiveCases) {
//            val actual = eval(read(tokenize(expression))).lastOrNull()
//            assertEquals("$expression == $actual: expected $expected", expected, actual)
//        }
//    }
}

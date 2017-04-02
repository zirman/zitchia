package com.robertchrzanowski.zitchia

sealed class Expression

sealed class List : Expression() {
    override fun toString() = "(${fold({ m, i -> if (m.isEmpty()) "$i" else "$m $i" }, "", this)})"
}

sealed class Atom : Expression()

class Cons(val head: Expression, val tail: List) : List() {
    override fun equals(other: Any?) =
        (((other as? Cons)?.head?.equals(head) ?: false) && (other as? Cons)?.tail?.equals(tail) ?: false)

    override fun hashCode(): Int {
        var result = head.hashCode()
        result += 31 * result + tail.hashCode()
        return result
    }
}

object Nil : List()

class Primitive<out T>(val value: T) : Atom() {
    override fun toString() = value.toString()
    override fun equals(other: Any?) = (other as? Primitive<*>)?.value?.equals(value) ?: false
    override fun hashCode() = value?.hashCode() ?: 0
}

data class Symbol(val symbol: String) : Atom() {
    override fun toString() = symbol
}

object Undefined : Atom() {
    override fun toString(): String = "undefined"
}

abstract class Function : Expression() {
    abstract fun apply(list: List): Expression
}

class Lambda(val ast: Cons, val closure: List) : Function() {
    override fun apply(list: List): Expression {
        val memo = LexicalScope
        LexicalScope = bindPairs(closure, ast.head as List, list)
        val expression = evalExpression((ast.tail as Cons).head)
        LexicalScope = memo
        return expression
    }

    override fun toString() = "Lambda <$ast> <$closure>"
}

class Recurse(ast: Cons, closure: List) : Function() {
    val closure = pushPairList(closure, (ast.head as Symbol), this)
    val ast = ast.tail

    override fun apply(list: List): Expression {
        val memo = LexicalScope
        LexicalScope = bindPairs(closure, (ast as Cons).head as List, list)
        val expression = evalExpression((ast.tail as Cons).head)
        LexicalScope = memo
        return expression
    }

    override fun toString() = "Recurse <$ast> <$closure>"
}

class Macro(val ast: Cons) : Function() {
    override fun apply(list: List): Expression {
        val memo = DynamicScope
        DynamicScope = bindPairs(DynamicScope, ast.head as List, list)
        val expression = evalExpression((ast.tail as Cons).head)
        DynamicScope = memo
        return evalExpression(expression)
    }

    override fun toString() = "Macro <$ast>"
}

val symbolTable: MutableMap<String, Symbol> = HashMap()

fun SymbolFactory(symbol: String): Symbol {
    val memo = symbolTable[symbol]

    return when {
        memo !== null ->
            memo

        else -> {
            val init = Symbol(symbol)
            symbolTable[symbol] = init
            init
        }
    }
}

val TruePrimitive = Primitive(true)
val FalsePrimative = Primitive(false)

fun bindPairs(list: List, keys: List, values: List): List = when {
    keys === Nil ->
        list

    ((keys as Cons).head as Symbol === SymbolFactory("...")) ->
        pushPairList(list, ((keys as Cons).tail as Cons).head as Symbol, values)

    else ->
        bindPairs(
            pushPairList(
                list,
                (keys as Cons).head as Symbol,
                (values as? Cons)?.head ?: Undefined),
            keys.tail,
            (values as? Cons)?.tail ?: Nil)
}

val TokenRegex = Regex("\\s*('|`|,|~|\\(|\\)|\"(\\\\.|[^\"])*\"|[^'`,()\"\\s]+)")

val QuoteSymbol = SymbolFactory("quote")
val QuasiquoteSymbol = SymbolFactory("quasiquote")
val UnquoteSymbol = SymbolFactory("unquote")
val IfSymbol = SymbolFactory("if")
val LambdaSymbol = SymbolFactory("lambda")
val MacroSymbol = SymbolFactory("macro")
val DynamicSymbol = SymbolFactory("dynamic")
val DefineSymbol = SymbolFactory("define")

val RecurseSymbol = SymbolFactory("recurse")

fun <T> fold(fn: (T, Expression) -> T, memo: T, list: List): T = when (list) {
    is Nil -> memo
    else -> fold(fn, fn(memo, (list as Cons).head), list.tail)
}

fun <T> foldRight(fn: (Expression, T) -> T, memo: T, list: List): T = when (list) {
    is Nil -> memo
    else -> fn((list as Cons).head, foldRight(fn, memo, list.tail))
}

fun tokenize(seq: CharSequence) = TokenRegex.findAll(seq).map { it.value.trim() }

fun read(tokens: Sequence<String>): Sequence<Expression> {
    val i = tokens.iterator()
    var token: String? = null

    fun parseExpression(): Expression {
        fun parseList(): List {
            token = i.next()

            return when {
                token.equals(")", false) ->
                    Nil

                else -> {
                    val expression = parseExpression()
                    val list = parseList()
                    Cons(expression, list)
                }
            }
        }

        fun parseAtom(): Atom {
            val string = token as String

            return when (string) {
                "true" -> TruePrimitive
                "false" -> FalsePrimative
                "undefined" -> Undefined

                else -> {
                    try {
                        Primitive(string.toDouble())
                    } catch (e: NumberFormatException) {
                        SymbolFactory(string)
                    }
                }
            }
        }

        return when (token?.toLowerCase()) {
            ")" -> throw Error("Unexpected Token: ')'")
            "(" -> parseList()

            "'" -> {
                token = i.next()
                Cons(QuoteSymbol, Cons(parseExpression(), Nil))
            }
            "`" -> {
                token = i.next()
                Cons(QuasiquoteSymbol, Cons(parseExpression(), Nil))
            }
            "," -> {
                token = i.next()
                Cons(UnquoteSymbol, Cons(parseExpression(), Nil))
            }
            "~" -> {
                token = i.next()
                Cons(DynamicSymbol, Cons(parseExpression(), Nil))
            }

            "quote" -> QuoteSymbol
            "quasiquote" -> QuasiquoteSymbol
            "unquote" -> UnquoteSymbol
            "if" -> IfSymbol
            "lambda" -> LambdaSymbol
            "macro" -> MacroSymbol
            "dynamic" -> DynamicSymbol
            "define" -> DefineSymbol
            "recurse" -> RecurseSymbol
            else -> parseAtom()
        }
    }

    return generateSequence {
        if (i.hasNext()) {
            token = i.next()
            parseExpression()
        } else null
    }
}

fun pushPairList(list: List, symbol: Symbol, expression: Expression) = Cons(Cons(symbol, Cons(expression, Nil)), list)

fun findPairList(list: List, symbol: Symbol): Expression = when {
    list === Nil ->
        Undefined

    symbol == ((list as Cons).head as Cons).head ->
        ((list.head as Cons).tail as Cons).head

    else ->
        findPairList(list.tail, symbol)
}

fun lessThanList(list: List, previous: Double = Double.NEGATIVE_INFINITY): Boolean = when {
    list === Nil -> true

    else -> {
        val value = ((list as Cons).head as Primitive<*>).value as Double
        previous < value && lessThanList(list.tail, value)
    }
}

fun greaterThanList(list: List, previous: Double = Double.POSITIVE_INFINITY): Boolean = when {
    list === Nil -> true

    else -> {
        val value = ((list as Cons).head as Primitive<*>).value as Double
        previous > value && greaterThanList(list.tail, value)
    }
}

fun lessThanOrEqualList(list: List, previous: Double = Double.NEGATIVE_INFINITY): Boolean = when {
    list === Nil -> true

    else -> {
        val value = ((list as Cons).head as Primitive<*>).value as Double
        previous <= value && lessThanOrEqualList(list.tail, value)
    }
}

fun greaterThanOrEqualList(list: List, previous: Double = Double.POSITIVE_INFINITY): Boolean = when {
    list === Nil -> true

    else -> {
        val value = ((list as Cons).head as Primitive<*>).value as Double
        previous >= value && greaterThanOrEqualList(list.tail, value)
    }
}

var Environment = {
    var scope: List = Nil

    scope = pushPairList(scope, SymbolFactory("*"), object : Function() {
        override fun apply(list: List) = Primitive(fold(
            { m, i -> m * (i as? Primitive<*>)?.value as Double },
            1.0,
            list))
    })

    scope = pushPairList(scope, SymbolFactory("/"), object : Function() {
        override fun apply(list: List) =
            Primitive(((list as Cons).head as Primitive<*>).value as Double /
                ((list.tail as Cons).head as Primitive<*>).value as Double)
    })

    scope = pushPairList(scope, SymbolFactory("+"), object : Function() {
        override fun apply(list: List) = Primitive(fold(
            { m, i -> m + (i as? Primitive<*>)?.value as Double },
            0.0,
            list))
    })

    scope = pushPairList(scope, SymbolFactory("-"), object : Function() {
        override fun apply(list: List) =
            Primitive(((list as Cons).head as Primitive<*>).value as Double -
                ((list.tail as Cons).head as Primitive<*>).value as Double)
    })

    scope = pushPairList(scope, SymbolFactory("<"), object : Function() {
        override fun apply(list: List) = if (lessThanList(list)) TruePrimitive else FalsePrimative
    })

    scope = pushPairList(scope, SymbolFactory(">"), object : Function() {
        override fun apply(list: List) = if (greaterThanList(list)) TruePrimitive else FalsePrimative
    })

    scope = pushPairList(scope, SymbolFactory("<="), object : Function() {
        override fun apply(list: List) = if (lessThanOrEqualList(list)) TruePrimitive else FalsePrimative
    })

    scope = pushPairList(scope, SymbolFactory(">="), object : Function() {
        override fun apply(list: List) = if (greaterThanOrEqualList(list)) TruePrimitive else FalsePrimative
    })

    scope = pushPairList(scope, SymbolFactory("cons"), object : Function() {
        override fun apply(list: List) = Cons((list as Cons).head, (list.tail as Cons).head as List)
    })

    scope = pushPairList(scope, SymbolFactory("cdr"), object : Function() {
        override fun apply(list: List) = ((list as Cons).head as Cons).tail
    })

    scope = pushPairList(scope, SymbolFactory("car"), object : Function() {
        override fun apply(list: List) = ((list as Cons).head as Cons).head
    })

    scope = pushPairList(scope, SymbolFactory("eval"), object : Function() {
        override fun apply(list: List) = evalExpression((list as Cons).head)
    })

    scope
}.invoke()

var LexicalScope: List = Nil
var DynamicScope: List = Nil

fun eval(expressions: Sequence<Expression>): Sequence<Expression> = expressions.map(::evalExpression)

fun evalExpression(expression: Expression): Expression = when (expression) {
    Nil -> Nil

    is Cons -> when (expression.head) {
        UnquoteSymbol -> throw Error("Unexpected token 'unquote'")
        QuoteSymbol -> (expression.tail as Cons).head
        QuasiquoteSymbol -> quasiEvalExpression((expression.tail as Cons).head)

        IfSymbol -> {
            val predicate = evalExpression((expression.tail as Cons).head)

            if (predicate !== Nil && predicate !== FalsePrimative && predicate !== Undefined) {
                evalExpression((expression.tail.tail as Cons).head)
            } else {
                evalExpression(((expression.tail.tail as Cons).tail as Cons).head)
            }
        }

        LambdaSymbol -> Lambda(expression.tail as Cons, LexicalScope)
        MacroSymbol -> Macro(expression.tail as Cons)
        DynamicSymbol -> findPairList(DynamicScope, (expression.tail as Cons).head as Symbol)

        DefineSymbol -> {
            val value = evalExpression(((expression.tail as Cons).tail as Cons).head)
            Environment = pushPairList(Environment, expression.tail.head as Symbol, value)
            value
        }

        RecurseSymbol -> Recurse(expression.tail as Cons, LexicalScope)

        else -> {
            val form = evalExpression(expression.head)

            when (form) {
                is Macro -> form.apply(expression.tail)
                is Function -> form.apply(evalList(expression.tail))
                else -> throw Exception("$form is not a function or macro")
            }
        }
    }

    is Symbol -> {
        val value = findPairList(LexicalScope, expression)
        if (value !== Undefined) value
        else findPairList(Environment, expression)
    }

    else -> expression
}

fun evalList(list: List) = foldRight<List>({ e, m -> Cons(evalExpression(e), m) }, Nil, list)

fun quasiEvalExpression(expression: Expression): Expression = when (expression) {
    Nil -> Nil

    is Cons -> when (expression.head) {
        UnquoteSymbol -> evalExpression((expression.tail as Cons).head)
        else -> quasiEvalList(expression)
    }

    else -> expression
}

fun quasiEvalList(list: List) = foldRight<List>({ e, m -> Cons(quasiEvalExpression(e), m) }, Nil, list)

val InitializeEnvironment = {
    for (i in eval(read(tokenize("""
        (define caar (lambda (list) (car (car list))))
        (define cdar (lambda (list) (cdr (car list))))
        (define cadr (lambda (list) (car (cdr list))))
        (define cddr (lambda (list) (cdr (cdr list))))

        (define caadr (lambda (list) (car (cadr list))))
        (define cdadr (lambda (list) (cdr (cadr list))))
        (define caddr (lambda (list) (car (cddr list))))
        (define cdddr (lambda (list) (cdr (cddr list))))

        (define caaar (lambda (list) (car (caar list))))
        (define cdaar (lambda (list) (cdr (caar list))))
        (define cadar (lambda (list) (car (cdar list))))
        (define cddar (lambda (list) (cdr (cdar list))))

        (define apply (lambda (name args) (eval (cons name args))))

        (define and (macro (... args) (if ~args `(if ,(car ~args) ,(cons 'and (cdr ~args)) ,(car ~args)) true)))
        (define or (macro (... args) (if ~args `(if ,(car ~args) ,(car ~args) ,(cons 'or (cdr ~args))) false)))
        (define cond (macro (... args) (if ~args `(if ,(car ~args) ,(cadr ~args) ,(cons 'cond (cddr ~args))) undefined)))
        (define defun (macro (name args ast) `(define ,~name (lambda ,~args ,~ast))))
""".trimMargin())))) {
    }
}.invoke()

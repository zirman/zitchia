package com.robertchrzanowski.zitchia

fun main(args: Array<String>) {
    generateSequence(::readLine)
            .map(::tokenize)
            .map(::read)
            .flatMap(::eval)
            .forEach { println("> $it") }
}

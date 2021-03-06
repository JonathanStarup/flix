/*
 *  Copyright 2021 Magnus Madsen
 *
 *  Licensed under the Apache License, Version 2.0 (the "License");
 *  you may not use this file except in compliance with the License.
 *  You may obtain a copy of the License at
 *
 *  http://www.apache.org/licenses/LICENSE-2.0
 *
 *  Unless required by applicable law or agreed to in writing, software
 *  distributed under the License is distributed on an "AS IS" BASIS,
 *  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 *  See the License for the specific language governing permissions and
 *  limitations under the License.
 */

///
/// A type class for types that can be boxed.
///
lawless class Boxable[a] with Order[a], ToString[a] {

    ///
    /// Boxes the given `x`.
    ///
    pub def box(x: a): Boxed

    ///
    /// Unboxes the given `x`.
    ///
    pub def unbox(x: Boxed): a

}

namespace Boxable {

    ///
    /// Lifts the given function `f` to operate on boxed values.
    ///
    /// Note: Accepts a curried function, but returns a non-curried function.
    ///
    pub def lift1(f: t1 -> t): Boxed -> Boxed with Boxable[t1], Boxable[t] =
        (b1: Boxed) -> box(f(unbox(b1)))

    ///
    /// Lifts the given function `f` to operate on boxed values.
    ///
    /// Note: Accepts a curried function, but returns a non-curried function.
    ///
    pub def lift2(f: t1 -> t2 -> t): Boxed -> Boxed -> Boxed with Boxable[t1], Boxable[t2], Boxable[t] =
        (b1: Boxed) -> (b2: Boxed) -> box(f(unbox(b1), unbox(b2)))

    ///
    /// Lifts the given function `f` to operate on boxed values.
    ///
    /// Note: Accepts a curried function, but returns a non-curried function.
    ///
    pub def lift3(f: t1 -> t2 -> t3 -> t): Boxed -> Boxed -> Boxed -> Boxed with Boxable[t1], Boxable[t2], Boxable[t3], Boxable[t] =
        (b1: Boxed) -> (b2: Boxed) -> (b3: Boxed) -> box(f(unbox(b1), unbox(b2), unbox(b3)))

    ///
    /// Lifts the given function `f` to operate on boxed values.
    ///
    /// Note: Accepts a curried function, but returns a non-curried function.
    ///
    pub def lift4(f: t1 -> t2 -> t3 -> t4 -> t): Boxed -> Boxed -> Boxed -> Boxed -> Boxed with Boxable[t1], Boxable[t2], Boxable[t3], Boxable[t4], Boxable[t] =
        (b1: Boxed) -> (b2: Boxed) -> (b3: Boxed) -> (b4: Boxed) -> box(f(unbox(b1), unbox(b2), unbox(b3), unbox(b4)))

    ///
    /// Lifts the given function `f` to operate on boxed values.
    ///
    /// Note: Accepts a curried function, but returns a non-curried function.
    ///
    pub def lift5(f: t1 -> t2 -> t3 -> t4 -> t5 -> t): Boxed -> Boxed -> Boxed -> Boxed -> Boxed -> Boxed with Boxable[t1], Boxable[t2], Boxable[t3], Boxable[t4], Boxable[t5], Boxable[t] =
        (b1: Boxed) -> (b2: Boxed) -> (b3: Boxed) -> (b4: Boxed) -> (b5: Boxed) -> box(f(unbox(b1), unbox(b2), unbox(b3), unbox(b4), unbox(b5)))

    ///
    /// Lifts the given Boolean-valued function `f` to operate on boxed values.
    ///
    pub def lift1b(f: t1 -> Bool): Boxed -> Bool with Boxable[t1] =
        (b1: Boxed) -> f(unbox(b1))

    ///
    /// Lifts the given Boolean-valued function `f` to operate on boxed values.
    ///
    /// Note: Accepts a curried function, but returns a non-curried function.
    ///
    pub def lift2b(f: t1 -> t2 -> Bool): Boxed -> Boxed -> Bool with Boxable[t1], Boxable[t2] =
        (b1: Boxed) -> (b2: Boxed) -> f(unbox(b1), unbox(b2))

    ///
    /// Lifts the given Boolean-valued function `f` to operate on boxed values.
    ///
    /// Note: Accepts a curried function, but returns a non-curried function.
    ///
    pub def lift3b(f: t1 -> t2 -> t3 -> Bool): Boxed -> Boxed -> Boxed -> Bool with Boxable[t1], Boxable[t2], Boxable[t3] =
        (b1: Boxed) -> (b2: Boxed) -> (b3: Boxed) -> f(unbox(b1), unbox(b2), unbox(b3))

    ///
    /// Lifts the given Boolean-valued function `f` to operate on boxed values.
    ///
    /// Note: Accepts a curried function, but returns a non-curried function.
    ///
    pub def lift4b(f: t1 -> t2 -> t3 -> t4 -> Bool): Boxed -> Boxed -> Boxed -> Boxed -> Bool with Boxable[t1], Boxable[t2], Boxable[t3], Boxable[t4] =
        (b1: Boxed) -> (b2: Boxed) -> (b3: Boxed) -> (b4: Boxed) -> f(unbox(b1), unbox(b2), unbox(b3), unbox(b4))

    ///
    /// Lifts the given Boolean-valued function `f` to operate on boxed values.
    ///
    /// Note: Accepts a curried function, but returns a non-curried function.
    ///
    pub def lift5b(f: t1 -> t2 -> t3 -> t4 -> t5 -> Bool): Boxed -> Boxed -> Boxed -> Boxed -> Boxed -> Bool with Boxable[t1], Boxable[t2], Boxable[t3], Boxable[t4], Boxable[t5] =
        (b1: Boxed) -> (b2: Boxed) -> (b3: Boxed) -> (b4: Boxed) -> (b5: Boxed) -> f(unbox(b1), unbox(b2), unbox(b3), unbox(b4), unbox(b5))

}

instance Boxable[Unit] {
    pub def box(x: Unit): Boxed = {
        let value = x as ##java.lang.Object;
        let compare = (o1, o2) -> Order.compare(o1 as Unit, o2 as Unit);
        let toString = o -> ToString.toString(o as Unit);
        BoxedObject(value, compare, toString)
    }
    pub def unbox(_: Boxed): Unit = ()
}

instance Boxable[Bool] {
    pub def box(x: Bool): Boxed = BoxedBool(x)
    pub def unbox(x: Boxed): Bool = match x {
        case BoxedBool(v) => v
        case _            => ?bug
    }
}

instance Boxable[Char] {
    pub def box(x: Char): Boxed = BoxedChar(x)
    pub def unbox(x: Boxed): Char = match x {
        case BoxedChar(v) => v
        case _            => ?bug
    }
}

instance Boxable[Int8] {
    pub def box(x: Int8): Boxed = BoxedInt8(x)
    pub def unbox(x: Boxed): Int8 = match x {
        case BoxedInt8(v) => v
        case _            => ?bug
    }
}

instance Boxable[Int16] {
    pub def box(x: Int16): Boxed = BoxedInt16(x)
    pub def unbox(x: Boxed): Int16 = match x {
        case BoxedInt16(v) => v
        case _             => ?bug
    }
}

instance Boxable[Int32] {
    pub def box(x: Int32): Boxed = BoxedInt32(x)
    pub def unbox(x: Boxed): Int32 = match x {
        case BoxedInt32(v) => v
        case _             => ?bug
    }
}

instance Boxable[Int64] {
    pub def box(x: Int64): Boxed = BoxedInt64(x)
    pub def unbox(x: Boxed): Int64 = match x {
        case BoxedInt64(v) => v
        case _             => ?bug
    }
}

instance Boxable[Float32] {
    pub def box(x: Float32): Boxed = BoxedFloat32(x)
    pub def unbox(x: Boxed): Float32 = match x {
        case BoxedFloat32(v) => v
        case _               => ?bug
    }
}

instance Boxable[Float64] {
    pub def box(x: Float64): Boxed = BoxedFloat64(x)
    pub def unbox(x: Boxed): Float64 = match x {
        case BoxedFloat64(v) => v
        case _               => ?bug
    }
}

instance Boxable[BigInt] {
    pub def box(x: BigInt): Boxed = {
        let value = x as ##java.lang.Object;
        let compare = (o1, o2) -> Order.compare(o1 as BigInt, o2 as BigInt);
        let toString = o -> ToString.toString(o as BigInt);
        BoxedObject(value, compare, toString)
    }
    pub def unbox(x: Boxed): BigInt = match x {
        case BoxedObject(v, _, _) => v as BigInt
        case _                    => ?bug
    }
}

instance Boxable[String] {
    pub def box(x: String): Boxed = {
        let value = x as ##java.lang.Object;
        let compare = (o1, o2) -> Order.compare(o1 as String, o2 as String);
        let toString = o -> ToString.toString(o as String);
        BoxedObject(value, compare, toString)
    }
    pub def unbox(x: Boxed): String = match x {
        case BoxedObject(v, _, _) => v as String
        case _                    => ?bug
    }
}

instance Boxable[(a, b)] with Boxable[a], Boxable[b] {
    pub def box(x: (a, b)): Boxed = {
        let value = x as ##java.lang.Object;
        let compare = (o1, o2) -> Order.compare(o1 as (a, b), o2 as (a, b));
        let toString = o -> ToString.toString(o as (a, b));
        BoxedObject(value, compare, toString)
    }
    pub def unbox(x: Boxed): (a, b) = match x {
        case BoxedObject(v, _, _) => v as (a, b)
        case _                    => ?bug
    }
}

instance Boxable[(a, b, c)] with Boxable[a], Boxable[b], Boxable[c] {
    pub def box(x: (a, b, c)): Boxed = {
        let value = x as ##java.lang.Object;
        let compare = (o1, o2) -> Order.compare(o1 as (a, b, c), o2 as (a, b, c));
        let toString = o -> ToString.toString(o as (a, b, c));
        BoxedObject(value, compare, toString)
    }
    pub def unbox(x: Boxed): (a, b, c) = match x {
        case BoxedObject(v, _, _) => v as (a, b, c)
        case _                    => ?bug
    }
}

instance Boxable[(a, b, c, d)] with Boxable[a], Boxable[b], Boxable[c], Boxable[d] {
    pub def box(x: (a, b, c, d)): Boxed = {
        let value = x as ##java.lang.Object;
        let compare = (o1, o2) -> Order.compare(o1 as (a, b, c, d), o2 as (a, b, c, d));
        let toString = o -> ToString.toString(o as (a, b, c, d));
        BoxedObject(value, compare, toString)
    }
    pub def unbox(x: Boxed): (a, b, c, d) = match x {
        case BoxedObject(v, _, _) => v as (a, b, c, d)
        case _                    => ?bug
    }
}

instance Boxable[(a, b, c, d, e)] with Boxable[a], Boxable[b], Boxable[c], Boxable[d], Boxable[e] {
    pub def box(x: (a, b, c, d, e)): Boxed = {
        let value = x as ##java.lang.Object;
        let compare = (o1, o2) -> Order.compare(o1 as (a, b, c, d, e), o2 as (a, b, c, d, e));
        let toString = o -> ToString.toString(o as (a, b, c, d, e));
        BoxedObject(value, compare, toString)
    }
    pub def unbox(x: Boxed): (a, b, c, d, e) = match x {
        case BoxedObject(v, _, _) => v as (a, b, c, d, e)
        case _                    => ?bug
    }
}

instance Boxable[(a, b, c, d, e, f)] with Boxable[a], Boxable[b], Boxable[c], Boxable[d], Boxable[e], Boxable[f] {
    pub def box(x: (a, b, c, d, e, f)): Boxed = {
        let value = x as ##java.lang.Object;
        let compare = (o1, o2) -> Order.compare(o1 as (a, b, c, d, e, f), o2 as (a, b, c, d, e, f));
        let toString = o -> ToString.toString(o as (a, b, c, d, e, f));
        BoxedObject(value, compare, toString)
    }
    pub def unbox(x: Boxed): (a, b, c, d, e, f) = match x {
        case BoxedObject(v, _, _) => v as (a, b, c, d, e, f)
        case _                    => ?bug
    }
}

instance Boxable[(a, b, c, d, e, f, g)] with Boxable[a], Boxable[b], Boxable[c], Boxable[d], Boxable[e], Boxable[f], Boxable[g] {
    pub def box(x: (a, b, c, d, e, f, g)): Boxed = {
        let value = x as ##java.lang.Object;
        let compare = (o1, o2) -> Order.compare(o1 as (a, b, c, d, e, f, g), o2 as (a, b, c, d, e, f, g));
        let toString = o -> ToString.toString(o as (a, b, c, d, e, f, g));
        BoxedObject(value, compare, toString)
    }
    pub def unbox(x: Boxed): (a, b, c, d, e, f, g) = match x {
        case BoxedObject(v, _, _) => v as (a, b, c, d, e, f, g)
        case _                    => ?bug
    }
}

instance Boxable[(a, b, c, d, e, f, g, h)] with Boxable[a], Boxable[b], Boxable[c], Boxable[d], Boxable[e], Boxable[f], Boxable[g], Boxable[h] {
    pub def box(x: (a, b, c, d, e, f, g, h)): Boxed = {
        let value = x as ##java.lang.Object;
        let compare = (o1, o2) -> Order.compare(o1 as (a, b, c, d, e, f, g, h), o2 as (a, b, c, d, e, f, g, h));
        let toString = o -> ToString.toString(o as (a, b, c, d, e, f, g, h));
        BoxedObject(value, compare, toString)
    }
    pub def unbox(x: Boxed): (a, b, c, d, e, f, g, h) = match x {
        case BoxedObject(v, _, _) => v as (a, b, c, d, e, f, g, h)
        case _                    => ?bug
    }
}

instance Boxable[(a, b, c, d, e, f, g, h, i)] with Boxable[a], Boxable[b], Boxable[c], Boxable[d], Boxable[e], Boxable[f], Boxable[g], Boxable[h], Boxable[i] {
    pub def box(x: (a, b, c, d, e, f, g, h, i)): Boxed = {
        let value = x as ##java.lang.Object;
        let compare = (o1, o2) -> Order.compare(o1 as (a, b, c, d, e, f, g, h, i), o2 as (a, b, c, d, e, f, g, h, i));
        let toString = o -> ToString.toString(o as (a, b, c, d, e, f, g, h, i));
        BoxedObject(value, compare, toString)
    }
    pub def unbox(x: Boxed): (a, b, c, d, e, f, g, h, i) = match x {
        case BoxedObject(v, _, _) => v as (a, b, c, d, e, f, g, h, i)
        case _                    => ?bug
    }
}

instance Boxable[(a, b, c, d, e, f, g, h, i, j)] with Boxable[a], Boxable[b], Boxable[c], Boxable[d], Boxable[e], Boxable[f], Boxable[g], Boxable[h], Boxable[i], Boxable[j] {
    pub def box(x: (a, b, c, d, e, f, g, h, i, j)): Boxed = {
        let value = x as ##java.lang.Object;
        let compare = (o1, o2) -> Order.compare(o1 as (a, b, c, d, e, f, g, h, i, j), o2 as (a, b, c, d, e, f, g, h, i, j));
        let toString = o -> ToString.toString(o as (a, b, c, d, e, f, g, h, i, j));
        BoxedObject(value, compare, toString)
    }
    pub def unbox(x: Boxed): (a, b, c, d, e, f, g, h, i, j) = match x {
        case BoxedObject(v, _, _) => v as (a, b, c, d, e, f, g, h, i, j)
        case _                    => ?bug
    }
}

instance Boxable[(a, b, c, d, e, f, g, h, i, j, k)] with Boxable[a], Boxable[b], Boxable[c], Boxable[d], Boxable[e], Boxable[f], Boxable[g], Boxable[h], Boxable[i], Boxable[j], Boxable[k] {
    pub def box(x: (a, b, c, d, e, f, g, h, i, j, k)): Boxed = {
        let value = x as ##java.lang.Object;
        let compare = (o1, o2) -> Order.compare(o1 as (a, b, c, d, e, f, g, h, i, j, k), o2 as (a, b, c, d, e, f, g, h, i, j, k));
        let toString = o -> ToString.toString(o as (a, b, c, d, e, f, g, h, i, j, k));
        BoxedObject(value, compare, toString)
    }
    pub def unbox(x: Boxed): (a, b, c, d, e, f, g, h, i, j, k) = match x {
        case BoxedObject(v, _, _) => v as (a, b, c, d, e, f, g, h, i, j, k)
        case _                    => ?bug
    }
}

instance Boxable[(a, b, c, d, e, f, g, h, i, j, k, l)] with Boxable[a], Boxable[b], Boxable[c], Boxable[d], Boxable[e], Boxable[f], Boxable[g], Boxable[h], Boxable[i], Boxable[j], Boxable[k], Boxable[l] {
    pub def box(x: (a, b, c, d, e, f, g, h, i, j, k, l)): Boxed = {
        let value = x as ##java.lang.Object;
        let compare = (o1, o2) -> Order.compare(o1 as (a, b, c, d, e, f, g, h, i, j, k, l), o2 as (a, b, c, d, e, f, g, h, i, j, k, l));
        let toString = o -> ToString.toString(o as (a, b, c, d, e, f, g, h, i, j, k, l));
        BoxedObject(value, compare, toString)
    }
    pub def unbox(x: Boxed): (a, b, c, d, e, f, g, h, i, j, k, l) = match x {
        case BoxedObject(v, _, _) => v as (a, b, c, d, e, f, g, h, i, j, k, l)
        case _                    => ?bug
    }
}

instance Boxable[(a, b, c, d, e, f, g, h, i, j, k, l, m)] with Boxable[a], Boxable[b], Boxable[c], Boxable[d], Boxable[e], Boxable[f], Boxable[g], Boxable[h], Boxable[i], Boxable[j], Boxable[k], Boxable[l], Boxable[m] {
    pub def box(x: (a, b, c, d, e, f, g, h, i, j, k, l, m)): Boxed = {
        let value = x as ##java.lang.Object;
        let compare = (o1, o2) -> Order.compare(o1 as (a, b, c, d, e, f, g, h, i, j, k, l, m), o2 as (a, b, c, d, e, f, g, h, i, j, k, l, m));
        let toString = o -> ToString.toString(o as (a, b, c, d, e, f, g, h, i, j, k, l, m));
        BoxedObject(value, compare, toString)
    }
    pub def unbox(x: Boxed): (a, b, c, d, e, f, g, h, i, j, k, l, m) = match x {
        case BoxedObject(v, _, _) => v as (a, b, c, d, e, f, g, h, i, j, k, l, m)
        case _                    => ?bug
    }
}

instance Boxable[(a, b, c, d, e, f, g, h, i, j, k, l, m, n)] with Boxable[a], Boxable[b], Boxable[c], Boxable[d], Boxable[e], Boxable[f], Boxable[g], Boxable[h], Boxable[i], Boxable[j], Boxable[k], Boxable[l], Boxable[m], Boxable[n] {
    pub def box(x: (a, b, c, d, e, f, g, h, i, j, k, l, m, n)): Boxed = {
        let value = x as ##java.lang.Object;
        let compare = (o1, o2) -> Order.compare(o1 as (a, b, c, d, e, f, g, h, i, j, k, l, m, n), o2 as (a, b, c, d, e, f, g, h, i, j, k, l, m, n));
        let toString = o -> ToString.toString(o as (a, b, c, d, e, f, g, h, i, j, k, l, m, n));
        BoxedObject(value, compare, toString)
    }
    pub def unbox(x: Boxed): (a, b, c, d, e, f, g, h, i, j, k, l, m, n) = match x {
        case BoxedObject(v, _, _) => v as (a, b, c, d, e, f, g, h, i, j, k, l, m, n)
        case _                    => ?bug
    }
}

instance Boxable[(a, b, c, d, e, f, g, h, i, j, k, l, m, n, o)] with Boxable[a], Boxable[b], Boxable[c], Boxable[d], Boxable[e], Boxable[f], Boxable[g], Boxable[h], Boxable[i], Boxable[j], Boxable[k], Boxable[l], Boxable[m], Boxable[n], Boxable[o] {
    pub def box(x: (a, b, c, d, e, f, g, h, i, j, k, l, m, n, o)): Boxed = {
        let value = x as ##java.lang.Object;
        let compare = (o1, o2) -> Order.compare(o1 as (a, b, c, d, e, f, g, h, i, j, k, l, m, n, o), o2 as (a, b, c, d, e, f, g, h, i, j, k, l, m, n, o));
        let toString = o -> ToString.toString(o as (a, b, c, d, e, f, g, h, i, j, k, l, m, n, o));
        BoxedObject(value, compare, toString)
    }
    pub def unbox(x: Boxed): (a, b, c, d, e, f, g, h, i, j, k, l, m, n, o) = match x {
        case BoxedObject(v, _, _) => v as (a, b, c, d, e, f, g, h, i, j, k, l, m, n, o)
        case _                    => ?bug
    }
}

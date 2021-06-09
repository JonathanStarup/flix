namespace Inst {

    pub enum PBool {}
    pub enum PInt32 {}
    pub enum PInt64 {}
    pub enum PChar {}
    pub enum PString {}
    pub enum PUnit {}
    pub enum PArray {}
    pub enum PAny {}

    pub enum Yes {}

    lawless class Cat1[t] {}
    instance Cat1[PInt32]
    instance Cat1[PArray]
    lawless class Cat2[t] {}
    instance Cat2[PInt64] {}

    pub enum Expr[t] {
        case EBool(Bool)
        case EInt32(Int32)
        case EInt64(Int64)
        case EAdd(Expr[PInt32], Expr[PInt32])
        case EAddInt64(Expr[PInt64], Expr[PInt64])
        case EIndex(Expr[t], Expr[PInt32])
        case ETuple(List[Expr[PAny]])
        case EIfThenElse(Expr[PBool], Expr[t], Expr[t])
        case EArraySlice(Expr[PArray], Expr[PInt32], Expr[PInt32])
    }

    pub def compile(e: Expr[t], s: {| r}): {t0: t | r} = match e {
        case EBool(_) => ???
        case EAdd(e1, e2) =>
            s   |> lock
                |> compile(e1)
                |> compile(e2)
                |> iadd
                |> unlock
                |> done(e)
        case ETuple(exps) =>
            let _h = s |> compileExps(exps);
            ???
        case EIfThenElse(e1, e2, e3) =>
            let _h = s |> compile(e1);
            ???
        case EArraySlice(base, beginIndex, endIndex) =>
            s   |> compile(base)
                |> compile(beginIndex)
                |> compile(endIndex)
                |> swap
                |> dup_x1
                |> isub
                |> dup
                |> xnewarray
                |> dup_x2
                |> swap
                |> pushInt(0)
                |> swap
                |> systemArrayCopy
                |> swap
                |> pop
                |> done(e)
        case _ => ???
    }

    pub def compileExps(es: List[Expr[PAny]], s: {| r}): {t0: List[PAny] | r} = ???
    pub def done(e: Expr[t], s: {t0 : a | r}): {t0: t | r} = ???
    pub def compileBool(e: Expr[t], s: {| r}): {t0: PBool | r} = ???
    pub def compileInt32(e: Expr[t], s: {| r}): {t0: PInt32 | r} = ???
    pub def lock(s: {| r}): {locked: Yes | r} = ???
    pub def unlock(s: {locked: Yes | r}): {| r} = ???
    pub def throw(s: {t0 : a | r}): {throws: Yes | r} = ???
    pub def pushInt(x: a, s: {| r}): {t0: PInt32 | r} = ???
    pub def aload0(s: {l0: a | r}): {t0: a | r} with Cat1[a] = ???
    pub def aload1(s: {l1: a | r}): {t0: a | r} with Cat1[a] = ???
    pub def astore0(s: {s0: a, l0: a | r}): {l0: a | r} with Cat1[a] = ???
    pub def pop(s: {t0: a | r}): {| r} with Cat1[a] = ???
    pub def swap(s: {t0: a, t0 : b | r}): {t0: b, t0: a| r} = ???
    pub def dup(s: {t0: a | r}): {t0: a, t0: a | r} = ???
    pub def getfield(s: { s0: PString, s0: PAny | r}): {t0: a| r} = ???
    pub def dup_x1(s: {t0: a, t0 : b | r}): {t0: a, t0 : b, t0: a | r} = ???
    pub def dup_x2(s: {t0: a, t0 : b, t0 : c, t0 : d | r}): {t0: a, t0 : b, t0 : c, t0 : d, t0: a, t0 : b | r} with Cat1[a] = ???
 // F[R ** T4 ** T3 ** T2 ** T1] => F[R ** T2 ** T1 ** T4 ** T3 ** T2 ** T1]
    pub def iadd(s: {t0: PInt32, t0: PInt32 | r}): {t0: PInt32 | r} = ???
    pub def isub(s: {t0: PInt32, t0: PInt32 | r}): {t0: PInt32 | r} = ???
    pub def xnewarray(s: {t0: PInt32 | r}): {t0: PArray | r} = ???
    //pub def systemArrayCopy(s: {t0: PArray, t0: PInt32, t0: PArray, t0: PInt32, t0: PInt32 | r}): { | r} = ???
    pub def systemArrayCopy(s: {t0: PInt32, t0: PInt32, t0: PArray, t0: PInt32, t0: PArray | r}): { | r} = ???
    pub def foo(): Unit =
        let _s = {} |> pushInt(12) |> pushInt(42) |> pop;
        ()
}
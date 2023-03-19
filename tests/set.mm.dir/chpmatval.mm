include "cfn.mm"
include "wcel.mm"
include "w3a.mm"
include "co.mm"
include "cv.mm"
include "cfv.mm"
include "cvv.mm"
include "cmpt.mm"
include "wceq.mm"
include "chpmatfval.mm"
include "3adant3.mm"
include "fveq2.mm"
include "oveq2d.mm"
include "fveq2d.mm"
include "adantl.mm"
include "simp3.mm"
include "fvexd.mm"
include "fvmptd.mm"

theorem chpmatval
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cP: class P
  let cR: class R
  let cT: class T
  let c.x: class .x.
  let c.1: class .1.
  let cM: class M
  let c.mi: class .-
  let cN: class N
  let cV: class V
  let cX: class X
  let cY: class Y
  let vm: setvar m
  let vn: setvar n
  let vr: setvar r
  assume chpmatfval.c: |- C = ( N CharPlyMat R )
  assume chpmatfval.a: |- A = ( N Mat R )
  assume chpmatfval.b: |- B = ( Base ` A )
  assume chpmatfval.p: |- P = ( Poly1 ` R )
  assume chpmatfval.y: |- Y = ( N Mat P )
  assume chpmatfval.d: |- D = ( N maDet P )
  assume chpmatfval.s: |- .- = ( -g ` Y )
  assume chpmatfval.x: |- X = ( var1 ` R )
  assume chpmatfval.m: |- .x. = ( .s ` Y )
  assume chpmatfval.t: |- T = ( N matToPolyMat R )
  assume chpmatfval.i: |- .1. = ( 1r ` Y )


  assert |- ( ( N e. Fin /\ R e. V /\ M e. B ) -> ( C ` M ) = ( D ` ( ( X .x. .1. ) .- ( T ` M ) ) ) )

  proof
    cN
    cfn
    wcel
    #
    cR
    cV
    wcel
    #
    cM
    cB
    wcel
    #
    w3a
    #
    vm
    cM
    cX
    c.1
    c.x
    co
    #
    vm
    cv
    #
    cT
    cfv
    #
    c.mi
    co
    #
    cD
    cfv
    #
    @4
    cM
    cT
    cfv
    #
    c.mi
    co
    #
    cD
    cfv
    #
    cB
    cC
    cvv
    @0
    @1
    cC
    vm
    cB
    @8
    cmpt
    wceq
    @2
    cA
    cB
    cC
    cD
    cP
    cR
    cT
    c.x
    c.1
    vm
    c.mi
    cN
    cV
    cX
    cY
    chpmatfval.c
    chpmatfval.a
    chpmatfval.b
    chpmatfval.p
    chpmatfval.y
    chpmatfval.d
    chpmatfval.s
    chpmatfval.x
    chpmatfval.m
    chpmatfval.t
    chpmatfval.i
    chpmatfval
    3adant3
    @5
    cM
    wceq
    #
    @8
    @11
    wceq
    @3
    @12
    @7
    @10
    cD
    @12
    @6
    @9
    @4
    c.mi
    @5
    cM
    cT
    fveq2
    oveq2d
    fveq2d
    adantl
    @0
    @1
    @2
    simp3
    @3
    @10
    cD
    fvexd
    fvmptd
end

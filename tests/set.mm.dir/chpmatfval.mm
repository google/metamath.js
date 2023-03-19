include "cfn.mm"
include "wcel.mm"
include "wa.mm"
include "cchpmat.mm"
include "co.mm"
include "cv.mm"
include "cfv.mm"
include "cmpt.mm"
include "cvv.mm"
include "cmat.mm"
include "cbs.mm"
include "cv1.mm"
include "cpl1.mm"
include "cur.mm"
include "cvsca.mm"
include "cmat2pmat.mm"
include "csg.mm"
include "cmdat.mm"
include "cmpt2.mm"
include "wceq.mm"
include "df-chpmat.mm"
include "a1i.mm"
include "oveq12.mm"
include "syl6eqr.mm"
include "fveq2d.mm"
include "simpl.mm"
include "simpr.mm"
include "oveq12d.mm"
include "fveq2.mm"
include "adantl.mm"
include "oveq123d.mm"
include "fveq1d.mm"
include "fveq12d.mm"
include "mpteq12dv.mm"
include "elex.mm"
include "fvex.mm"
include "eqeltri.mm"
include "mptexg.mm"
include "mp1i.mm"
include "ovmpt2d.mm"
include "syl5eq.mm"

theorem chpmatfval
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cP: class P
  let cR: class R
  let cT: class T
  let c.x: class .x.
  let c.1: class .1.
  let vm: setvar m
  let c.mi: class .-
  let cN: class N
  let cV: class V
  let cX: class X
  let cY: class Y
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

  disjoint B m
  disjoint D m
  disjoint .1. m
  disjoint N m
  disjoint R m
  disjoint X m
  disjoint T m
  disjoint .x. m
  disjoint .- m
  disjoint m n
  disjoint m r
  disjoint n r
  disjoint B n
  disjoint B r
  disjoint D n
  disjoint D r
  disjoint .1. n
  disjoint .1. r
  disjoint N n
  disjoint N r
  disjoint R n
  disjoint R r
  disjoint X n
  disjoint X r
  disjoint T n
  disjoint T r
  disjoint V n
  disjoint V r
  disjoint .x. n
  disjoint .x. r
  disjoint .- n
  disjoint .- r
  assert |- ( ( N e. Fin /\ R e. V ) -> C = ( m e. B |-> ( D ` ( ( X .x. .1. ) .- ( T ` m ) ) ) ) )

  proof
    cN
    cfn
    wcel
    #
    cR
    cV
    wcel
    #
    wa
    #
    cC
    cN
    cR
    cchpmat
    co
    vm
    cB
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
    cmpt
    #
    chpmatfval.c
    @2
    vn
    vr
    cN
    cR
    cfn
    cvv
    vm
    vn
    cv
    #
    vr
    cv
    #
    cmat
    co
    #
    cbs
    cfv
    #
    @10
    cv1
    cfv
    #
    @9
    @10
    cpl1
    cfv
    #
    cmat
    co
    #
    cur
    cfv
    #
    @15
    cvsca
    cfv
    #
    co
    #
    @4
    @9
    @10
    cmat2pmat
    co
    #
    cfv
    #
    @15
    csg
    cfv
    #
    co
    #
    @9
    @14
    cmdat
    co
    #
    cfv
    #
    cmpt
    #
    @8
    cchpmat
    cvv
    cchpmat
    vn
    vr
    cfn
    cvv
    @25
    cmpt2
    wceq
    @2
    vm
    vn
    vr
    df-chpmat
    a1i
    @9
    cN
    wceq
    #
    @10
    cR
    wceq
    #
    wa
    #
    @25
    @8
    wceq
    @2
    @28
    vm
    @12
    @24
    cB
    @7
    @28
    @12
    cA
    cbs
    cfv
    #
    cB
    @28
    @11
    cA
    cbs
    @28
    @11
    cN
    cR
    cmat
    co
    cA
    @9
    cN
    @10
    cR
    cmat
    oveq12
    chpmatfval.a
    syl6eqr
    fveq2d
    chpmatfval.b
    syl6eqr
    @28
    @22
    @6
    @23
    cD
    @28
    @23
    cN
    cP
    cmdat
    co
    cD
    @28
    @9
    cN
    @14
    cP
    cmdat
    @26
    @27
    simpl
    #
    @28
    @14
    cR
    cpl1
    cfv
    #
    cP
    @28
    @10
    cR
    cpl1
    @26
    @27
    simpr
    fveq2d
    chpmatfval.p
    syl6eqr
    oveq12d
    chpmatfval.d
    syl6eqr
    @28
    @18
    @3
    @20
    @5
    @21
    c.mi
    @28
    @21
    cY
    csg
    cfv
    c.mi
    @28
    @15
    cY
    csg
    @28
    @15
    cN
    cP
    cmat
    co
    cY
    @28
    @9
    cN
    @14
    cP
    cmat
    @30
    @28
    @14
    @31
    cP
    @27
    @14
    @31
    wceq
    @26
    @10
    cR
    cpl1
    fveq2
    adantl
    chpmatfval.p
    syl6eqr
    oveq12d
    chpmatfval.y
    syl6eqr
    #
    fveq2d
    chpmatfval.s
    syl6eqr
    @28
    @13
    cX
    @16
    c.1
    @17
    c.x
    @28
    @17
    cY
    cvsca
    cfv
    c.x
    @28
    @15
    cY
    cvsca
    @32
    fveq2d
    chpmatfval.m
    syl6eqr
    @27
    @13
    cX
    wceq
    @26
    @27
    @13
    cR
    cv1
    cfv
    cX
    @10
    cR
    cv1
    fveq2
    chpmatfval.x
    syl6eqr
    adantl
    @28
    @16
    cY
    cur
    cfv
    c.1
    @28
    @15
    cY
    cur
    @32
    fveq2d
    chpmatfval.i
    syl6eqr
    oveq123d
    @28
    @4
    @19
    cT
    @28
    @19
    cN
    cR
    cmat2pmat
    co
    cT
    @9
    cN
    @10
    cR
    cmat2pmat
    oveq12
    chpmatfval.t
    syl6eqr
    fveq1d
    oveq123d
    fveq12d
    mpteq12dv
    adantl
    @0
    @1
    simpl
    @1
    cR
    cvv
    wcel
    @0
    cR
    cV
    elex
    adantl
    cB
    cvv
    wcel
    @8
    cvv
    wcel
    @2
    cB
    @29
    cvv
    chpmatfval.b
    cA
    cbs
    fvex
    eqeltri
    vm
    cB
    @7
    cvv
    mptexg
    mp1i
    ovmpt2d
    syl5eq
end

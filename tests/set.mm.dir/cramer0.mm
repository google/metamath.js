include "c0.mm"
include "wceq.mm"
include "ccrg.mm"
include "wcel.mm"
include "wa.mm"
include "cfv.mm"
include "cui.mm"
include "cv.mm"
include "cmatrepV.mm"
include "co.mm"
include "cmpt.mm"
include "wi.mm"
include "csn.mm"
include "cmat.mm"
include "cbs.mm"
include "fveq2i.mm"
include "eqtri.mm"
include "oveq1.mm"
include "fveq2d.mm"
include "syl5eq.mm"
include "adantr.mm"
include "eleq2d.mm"
include "wb.mm"
include "mat0dimbas0.mm"
include "adantl.mm"
include "bitrd.mm"
include "c1o.mm"
include "cmap.mm"
include "a1i.mm"
include "oveq2.mm"
include "cvv.mm"
include "fvex.mm"
include "map0e.mm"
include "mp1i.mm"
include "3eqtrd.mm"
include "el1o.mm"
include "syl6bb.mm"
include "anbi12d.mm"
include "elsni.mm"
include "mpteq1.mm"
include "mpt0.mm"
include "syl6eq.mm"
include "eqeq2d.mm"
include "ad2antrr.mm"
include "simplrl.mm"
include "simpr.mm"
include "oveq12d.mm"
include "mavmul0.mm"
include "eqcomd.mm"
include "ad2antlr.mm"
include "ex.mm"
include "sylbid.mm"
include "a1d.mm"
include "sylani.mm"
include "3imp.mm"

theorem cramer0
  let cA: class A
  let cB: class B
  let cD: class D
  let c.dv: class ./
  let cR: class R
  let c.x: class .x.
  let vi: setvar i
  let cN: class N
  let cV: class V
  let cX: class X
  let cY: class Y
  let cZ: class Z
  let va: setvar a
  let vz: setvar z
  let vv: setvar v
  assume cramer.a: |- A = ( N Mat R )
  assume cramer.b: |- B = ( Base ` A )
  assume cramer.v: |- V = ( ( Base ` R ) ^m N )
  assume cramer.d: |- D = ( N maDet R )
  assume cramer.x: |- .x. = ( R maVecMul <. N , N >. )
  assume cramer.q: |- ./ = ( /r ` R )

  disjoint B i
  disjoint D i
  disjoint N i
  disjoint R i
  disjoint V i
  disjoint X i
  disjoint Y i
  disjoint Z i
  disjoint .x. i
  disjoint ./ i
  disjoint A a
  disjoint B a
  disjoint a i
  disjoint D a
  disjoint N a
  disjoint R a
  disjoint V a
  disjoint X a
  disjoint Y a
  disjoint Z a
  disjoint .x. a
  disjoint ./ a
  disjoint B z
  disjoint D z
  disjoint N z
  disjoint i z
  disjoint R z
  disjoint V z
  disjoint X z
  disjoint Y z
  disjoint A v
  disjoint A z
  disjoint v z
  disjoint B v
  disjoint D v
  disjoint N v
  disjoint i v
  disjoint R v
  disjoint V v
  disjoint X v
  disjoint Y v
  disjoint .x. v
  disjoint .x. z
  disjoint ./ v
  disjoint ./ z
  assert |- ( ( ( N = (/) /\ R e. CRing ) /\ ( X e. B /\ Y e. V ) /\ ( D ` X ) e. ( Unit ` R ) ) -> ( Z = ( i e. N |-> ( ( D ` ( ( X ( N matRepV R ) Y ) ` i ) ) ./ ( D ` X ) ) ) -> ( X .x. Z ) = Y ) )

  proof
    cN
    c0
    wceq
    #
    cR
    ccrg
    wcel
    #
    wa
    #
    cX
    cB
    wcel
    #
    cY
    cV
    wcel
    #
    wa
    #
    cX
    cD
    cfv
    #
    cR
    cui
    cfv
    wcel
    #
    cZ
    vi
    cN
    vi
    cv
    cX
    cY
    cN
    cR
    cmatrepV
    co
    co
    cfv
    cD
    cfv
    @6
    c.dv
    co
    #
    cmpt
    #
    wceq
    #
    cX
    cZ
    c.x
    co
    #
    cY
    wceq
    #
    wi
    #
    @2
    @5
    cX
    c0
    csn
    #
    wcel
    #
    cY
    c0
    wceq
    #
    wa
    @7
    @13
    wi
    #
    @2
    @3
    @15
    @4
    @16
    @2
    @3
    cX
    c0
    cR
    cmat
    co
    #
    cbs
    cfv
    #
    wcel
    #
    @15
    @2
    cB
    @19
    cX
    @0
    cB
    @19
    wceq
    @1
    @0
    cB
    cN
    cR
    cmat
    co
    #
    cbs
    cfv
    #
    @19
    cB
    cA
    cbs
    cfv
    @22
    cramer.b
    cA
    @21
    cbs
    cramer.a
    fveq2i
    eqtri
    @0
    @21
    @18
    cbs
    cN
    c0
    cR
    cmat
    oveq1
    fveq2d
    syl5eq
    adantr
    eleq2d
    @1
    @20
    @15
    wb
    @0
    @1
    @19
    @14
    cX
    cR
    ccrg
    mat0dimbas0
    eleq2d
    adantl
    bitrd
    @2
    @4
    cY
    c1o
    wcel
    @16
    @2
    cV
    c1o
    cY
    @2
    cV
    cR
    cbs
    cfv
    #
    cN
    cmap
    co
    #
    @23
    c0
    cmap
    co
    #
    c1o
    cV
    @24
    wceq
    @2
    cramer.v
    a1i
    @0
    @24
    @25
    wceq
    @1
    cN
    c0
    @23
    cmap
    oveq2
    adantr
    @23
    cvv
    wcel
    @25
    c1o
    wceq
    @2
    cR
    cbs
    fvex
    @23
    cvv
    map0e
    mp1i
    3eqtrd
    eleq2d
    cY
    el1o
    syl6bb
    anbi12d
    @15
    @2
    cX
    c0
    wceq
    #
    @16
    @17
    cX
    c0
    elsni
    @2
    @26
    @16
    wa
    #
    @17
    @2
    @27
    wa
    #
    @13
    @7
    @28
    @10
    cZ
    c0
    wceq
    #
    @12
    @0
    @10
    @29
    wb
    @1
    @27
    @0
    @9
    c0
    cZ
    @0
    @9
    vi
    c0
    @8
    cmpt
    c0
    vi
    cN
    c0
    @8
    mpteq1
    vi
    @8
    mpt0
    syl6eq
    eqeq2d
    ad2antrr
    @28
    @29
    @12
    @28
    @29
    wa
    #
    @11
    c0
    c0
    c.x
    co
    #
    c0
    cY
    @30
    cX
    c0
    cZ
    c0
    c.x
    @2
    @26
    @16
    @29
    simplrl
    @28
    @29
    simpr
    oveq12d
    @2
    @31
    c0
    wceq
    @27
    @29
    cR
    c.x
    cN
    ccrg
    cramer.x
    mavmul0
    ad2antrr
    @27
    c0
    cY
    wceq
    @2
    @29
    @27
    cY
    c0
    @26
    @16
    simpr
    eqcomd
    ad2antlr
    3eqtrd
    ex
    sylbid
    a1d
    ex
    sylani
    sylbid
    3imp
end

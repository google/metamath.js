include "c0.mm"
include "wne.mm"
include "ccrg.mm"
include "wcel.mm"
include "wa.mm"
include "cfv.mm"
include "cui.mm"
include "w3a.mm"
include "cv.mm"
include "co.mm"
include "wceq.mm"
include "wrex.mm"
include "cmatrepV.mm"
include "cmpt.mm"
include "wi.mm"
include "slesolex.mm"
include "wral.mm"
include "cramerlem2.mm"
include "3adant1l.mm"
include "weq.mm"
include "oveq2.mm"
include "eqeq1d.mm"
include "rexraleqim.mm"
include "adantl.mm"
include "simpl.mm"
include "eqtrd.mm"
include "ex.mm"
include "a1d.mm"
include "syl.mm"
include "expcom.mm"
include "com23.mm"
include "mpcom.mm"
include "mpd.mm"

theorem cramerlem3
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
  assert |- ( ( ( N =/= (/) /\ R e. CRing ) /\ ( X e. B /\ Y e. V ) /\ ( D ` X ) e. ( Unit ` R ) ) -> ( Z = ( i e. N |-> ( ( D ` ( ( X ( N matRepV R ) Y ) ` i ) ) ./ ( D ` X ) ) ) -> ( X .x. Z ) = Y ) )

  proof
    cN
    c0
    wne
    #
    cR
    ccrg
    wcel
    #
    wa
    cX
    cB
    wcel
    cY
    cV
    wcel
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
    w3a
    #
    cX
    vv
    cv
    #
    c.x
    co
    #
    cY
    wceq
    #
    vv
    cV
    wrex
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
    @3
    c.dv
    co
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
    vv
    cA
    cB
    cD
    cR
    c.x
    cN
    cV
    cX
    cY
    cramer.a
    cramer.b
    cramer.v
    cramer.x
    cramer.d
    slesolex
    cX
    vz
    cv
    #
    c.x
    co
    #
    cY
    wceq
    #
    @15
    @10
    wceq
    wi
    vz
    cV
    wral
    #
    @5
    @9
    @14
    wi
    @1
    @2
    @4
    @18
    @0
    vz
    cA
    cB
    cD
    c.dv
    cR
    c.x
    vi
    cN
    cV
    cX
    cY
    cramer.a
    cramer.b
    cramer.v
    cramer.d
    cramer.x
    cramer.q
    cramerlem2
    3adant1l
    @18
    @9
    @5
    @14
    @9
    @18
    @5
    @14
    wi
    #
    @9
    @18
    wa
    cX
    @10
    c.x
    co
    #
    cY
    wceq
    #
    @19
    @8
    @17
    @21
    vz
    vv
    cV
    @10
    vz
    vv
    weq
    @16
    @7
    cY
    @15
    @6
    cX
    c.x
    oveq2
    eqeq1d
    @6
    @10
    wceq
    @7
    @20
    cY
    @6
    @10
    cX
    c.x
    oveq2
    eqeq1d
    rexraleqim
    @21
    @14
    @5
    @21
    @11
    @13
    @21
    @11
    wa
    @12
    @20
    cY
    @11
    @12
    @20
    wceq
    @21
    cZ
    @10
    cX
    c.x
    oveq2
    adantl
    @21
    @11
    simpl
    eqtrd
    ex
    a1d
    syl
    expcom
    com23
    mpcom
    mpd
end

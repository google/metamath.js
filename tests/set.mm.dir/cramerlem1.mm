include "ccrg.mm"
include "wcel.mm"
include "wa.mm"
include "cfv.mm"
include "cui.mm"
include "co.mm"
include "wceq.mm"
include "w3a.mm"
include "cv.mm"
include "cmatrepV.mm"
include "cmpt.mm"
include "wral.mm"
include "simp1.mm"
include "anim1i.mm"
include "simpl2.mm"
include "pm3.22.mm"
include "3adant2.mm"
include "3ad2ant3.mm"
include "adantr.mm"
include "cur.mm"
include "eqid.mm"
include "cramerimp.mm"
include "syl3anc.mm"
include "ralrimiva.mm"
include "cvv.mm"
include "wfn.mm"
include "cbs.mm"
include "cmap.mm"
include "elmapfn.mm"
include "eleq2s.mm"
include "3ad2ant2.mm"
include "weq.mm"
include "fveq2.mm"
include "fveq2d.mm"
include "oveq1d.mm"
include "ovexd.mm"
include "fnmptfvd.mm"
include "mpbird.mm"

theorem cramerlem1
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
  assert |- ( ( R e. CRing /\ ( X e. B /\ Y e. V ) /\ ( ( D ` X ) e. ( Unit ` R ) /\ Z e. V /\ ( X .x. Z ) = Y ) ) -> Z = ( i e. N |-> ( ( D ` ( ( X ( N matRepV R ) Y ) ` i ) ) ./ ( D ` X ) ) ) )

  proof
    cR
    ccrg
    wcel
    #
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
    cZ
    cV
    wcel
    #
    cX
    cZ
    c.x
    co
    cY
    wceq
    #
    w3a
    #
    w3a
    #
    cZ
    vi
    cN
    vi
    cv
    #
    cX
    cY
    cN
    cR
    cmatrepV
    co
    #
    co
    #
    cfv
    #
    cD
    cfv
    #
    @2
    c.dv
    co
    #
    cmpt
    wceq
    va
    cv
    #
    cZ
    cfv
    @14
    @10
    cfv
    #
    cD
    cfv
    #
    @2
    c.dv
    co
    #
    wceq
    #
    va
    cN
    wral
    @7
    @18
    va
    cN
    @7
    @14
    cN
    wcel
    #
    wa
    #
    @0
    @19
    wa
    @1
    @5
    @3
    wa
    #
    @18
    @7
    @0
    @19
    @0
    @1
    @6
    simp1
    anim1i
    @0
    @1
    @6
    @19
    simpl2
    @7
    @21
    @19
    @6
    @0
    @21
    @1
    @3
    @5
    @21
    @4
    @3
    @5
    pm3.22
    3adant2
    3ad2ant3
    adantr
    cA
    cB
    cD
    c.dv
    cR
    c.x
    @14
    cA
    cur
    cfv
    cZ
    @9
    co
    cfv
    #
    @15
    @14
    cN
    cV
    cX
    cY
    cZ
    cramer.a
    cramer.b
    cramer.v
    @22
    eqid
    @15
    eqid
    cramer.x
    cramer.d
    cramer.q
    cramerimp
    syl3anc
    ralrimiva
    @7
    cN
    @13
    @17
    cvv
    va
    cZ
    cvv
    vi
    @6
    @0
    cZ
    cN
    wfn
    #
    @1
    @4
    @3
    @23
    @5
    @23
    cZ
    cR
    cbs
    cfv
    #
    cN
    cmap
    co
    cV
    cZ
    @24
    cN
    elmapfn
    cramer.v
    eleq2s
    3ad2ant2
    3ad2ant3
    va
    vi
    weq
    #
    @16
    @12
    @2
    c.dv
    @25
    @15
    @11
    cD
    @14
    @8
    @10
    fveq2
    fveq2d
    oveq1d
    @20
    @16
    @2
    c.dv
    ovexd
    @7
    @8
    cN
    wcel
    wa
    @12
    @2
    c.dv
    ovexd
    fnmptfvd
    mpbird
end

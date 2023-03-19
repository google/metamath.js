include "cxp.mm"
include "wfn.mm"
include "wcel.mm"
include "w3a.mm"
include "wa.mm"
include "ccur.mm"
include "cfv.mm"
include "cv.mm"
include "cop.mm"
include "cmpt.mm"
include "co.mm"
include "wceq.mm"
include "dffn5.mm"
include "cureq.mm"
include "sylbi.mm"
include "adantr.mm"
include "cvv.mm"
include "fveq2.mm"
include "mpt2mpt.mm"
include "wral.mm"
include "fvex.mm"
include "rgen2w.mm"
include "a1i.mm"
include "c0.mm"
include "wne.mm"
include "ne0i.mm"
include "adantl.mm"
include "mpt2curryd.mm"
include "eqtrd.mm"
include "3adant2.mm"
include "fveq1d.mm"
include "mptexg.mm"
include "opeq1.mm"
include "fveq2d.mm"
include "mpteq2dv.mm"
include "eqid.mm"
include "fvmptg.mm"
include "sylan2.mm"
include "3ad2antl2.mm"
include "opeq2.mm"
include "fvmpt.mm"
include "df-ov.mm"
include "syl6eqr.mm"
include "3ad2ant3.mm"

theorem curfv
  let cA: class A
  let cB: class B
  let cF: class F
  let cV: class V
  let cW: class W
  let cX: class X
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cC: class C


  assert |- ( ( ( F Fn ( V X. W ) /\ A e. V /\ B e. W ) /\ W e. X ) -> ( ( curry F ` A ) ` B ) = ( A F B ) )

  proof
    cF
    cV
    cW
    cxp
    #
    wfn
    #
    cA
    cV
    wcel
    #
    cB
    cW
    wcel
    #
    w3a
    #
    cW
    cX
    wcel
    #
    wa
    #
    cB
    cA
    cF
    ccur
    #
    cfv
    #
    cfv
    cB
    vy
    cW
    cA
    vy
    cv
    #
    cop
    #
    cF
    cfv
    #
    cmpt
    #
    cfv
    #
    cA
    cB
    cF
    co
    #
    @6
    cB
    @8
    @12
    @6
    @8
    cA
    vx
    cV
    vy
    cW
    vx
    cv
    #
    @9
    cop
    #
    cF
    cfv
    #
    cmpt
    #
    cmpt
    #
    cfv
    #
    @12
    @4
    @8
    @20
    wceq
    @5
    @4
    cA
    @7
    @19
    @1
    @3
    @7
    @19
    wceq
    @2
    @1
    @3
    wa
    #
    @7
    vz
    @0
    vz
    cv
    #
    cF
    cfv
    #
    cmpt
    #
    ccur
    #
    @19
    @1
    @7
    @25
    wceq
    #
    @3
    @1
    cF
    @24
    wceq
    @26
    vz
    @0
    cF
    dffn5
    cF
    @24
    cureq
    sylbi
    adantr
    @21
    vx
    vy
    @17
    @24
    cvv
    cV
    cW
    vx
    vy
    vz
    cV
    cW
    @23
    @17
    @22
    @16
    cF
    fveq2
    mpt2mpt
    @17
    cvv
    wcel
    #
    vy
    cW
    wral
    vx
    cV
    wral
    @21
    @27
    vx
    vy
    cV
    cW
    @16
    cF
    fvex
    rgen2w
    a1i
    @3
    cW
    c0
    wne
    @1
    cW
    cB
    ne0i
    adantl
    mpt2curryd
    eqtrd
    3adant2
    fveq1d
    adantr
    @2
    @1
    @5
    @20
    @12
    wceq
    #
    @3
    @5
    @2
    @12
    cvv
    wcel
    @28
    vy
    cW
    @11
    cX
    mptexg
    vx
    cA
    @18
    @12
    cV
    cvv
    @19
    @15
    cA
    wceq
    #
    vy
    cW
    @17
    @11
    @29
    @16
    @10
    cF
    @15
    cA
    @9
    opeq1
    fveq2d
    mpteq2dv
    @19
    eqid
    fvmptg
    sylan2
    3ad2antl2
    eqtrd
    fveq1d
    @4
    @13
    @14
    wceq
    #
    @5
    @3
    @1
    @30
    @2
    @3
    @13
    cA
    cB
    cop
    #
    cF
    cfv
    #
    @14
    vy
    cB
    @11
    @32
    cW
    @12
    @9
    cB
    wceq
    @10
    @31
    cF
    @9
    cB
    cA
    opeq2
    fveq2d
    @12
    eqid
    @31
    cF
    fvex
    fvmpt
    cA
    cB
    cF
    df-ov
    syl6eqr
    3ad2ant3
    adantr
    eqtrd
end

include "cmap.mm"
include "co.mm"
include "wf.mm"
include "c0.mm"
include "wne.mm"
include "wa.mm"
include "cv.mm"
include "cfv.mm"
include "cmpt.mm"
include "cunc.mm"
include "ccur.mm"
include "simpl.mm"
include "feqmptd.mm"
include "cdm.mm"
include "cop.mm"
include "wbr.mm"
include "copab.mm"
include "cxp.mm"
include "wceq.mm"
include "uncf.mm"
include "fdm.mm"
include "syl.mm"
include "dmeqd.mm"
include "dmxp.mm"
include "sylan9eq.mm"
include "eqcomd.mm"
include "wcel.mm"
include "df-mpt.mm"
include "ffvelrn.mm"
include "elmapi.mm"
include "wb.mm"
include "wfun.mm"
include "ffun.mm"
include "funbrfv2b.mm"
include "3syl.mm"
include "adantr.mm"
include "eleq2d.mm"
include "opelxp.mm"
include "baib.mm"
include "sylan9bb.mm"
include "df-ov.mm"
include "cvv.mm"
include "vex.mm"
include "uncov.mm"
include "mp2an.mm"
include "eqtr3i.mm"
include "eqeq1i.mm"
include "eqcom.mm"
include "bitri.mm"
include "a1i.mm"
include "anbi12d.mm"
include "bitrd.mm"
include "opabbidv.mm"
include "3eqtr4a.mm"
include "adantlr.mm"
include "mpteq12dva.mm"
include "df-cur.mm"
include "syl6eqr.mm"
include "eqtr2d.mm"

theorem curunc
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cV: class V
  let cW: class W


  assert |- ( ( F : A --> ( C ^m B ) /\ B =/= (/) ) -> curry uncurry F = F )

  proof
    cA
    cC
    cB
    cmap
    co
    #
    cF
    wf
    #
    cB
    c0
    wne
    #
    wa
    #
    cF
    vx
    cA
    vx
    cv
    #
    cF
    cfv
    #
    cmpt
    #
    cF
    cunc
    #
    ccur
    #
    @3
    vx
    cA
    @0
    cF
    @1
    @2
    simpl
    feqmptd
    @3
    @6
    vx
    @7
    cdm
    #
    cdm
    #
    @4
    vy
    cv
    #
    cop
    #
    vz
    cv
    #
    @7
    wbr
    #
    vy
    vz
    copab
    #
    cmpt
    @8
    @3
    vx
    cA
    @5
    @10
    @15
    @3
    @10
    cA
    @1
    @2
    @10
    cA
    cB
    cxp
    #
    cdm
    cA
    @1
    @9
    @16
    @1
    @16
    cC
    @7
    wf
    #
    @9
    @16
    wceq
    cA
    cB
    cC
    cF
    uncf
    #
    @16
    cC
    @7
    fdm
    syl
    #
    dmeqd
    cA
    cB
    dmxp
    sylan9eq
    eqcomd
    @1
    @4
    cA
    wcel
    #
    @5
    @15
    wceq
    @2
    @1
    @20
    wa
    #
    vy
    cB
    @11
    @5
    cfv
    #
    cmpt
    @11
    cB
    wcel
    #
    @13
    @22
    wceq
    #
    wa
    #
    vy
    vz
    copab
    @5
    @15
    vy
    vz
    cB
    @22
    df-mpt
    @21
    vy
    cB
    cC
    @5
    @21
    @5
    @0
    wcel
    cB
    cC
    @5
    wf
    cA
    @0
    @4
    cF
    ffvelrn
    @5
    cC
    cB
    elmapi
    syl
    feqmptd
    @21
    @14
    @25
    vy
    vz
    @21
    @14
    @12
    @9
    wcel
    #
    @12
    @7
    cfv
    #
    @13
    wceq
    #
    wa
    #
    @25
    @1
    @14
    @29
    wb
    #
    @20
    @1
    @17
    @7
    wfun
    @30
    @18
    @16
    cC
    @7
    ffun
    @12
    @13
    @7
    funbrfv2b
    3syl
    adantr
    @21
    @26
    @23
    @28
    @24
    @1
    @26
    @12
    @16
    wcel
    #
    @20
    @23
    @1
    @9
    @16
    @12
    @19
    eleq2d
    @31
    @20
    @23
    @4
    @11
    cA
    cB
    opelxp
    baib
    sylan9bb
    @28
    @24
    wb
    @21
    @28
    @22
    @13
    wceq
    @24
    @27
    @22
    @13
    @4
    @11
    @7
    co
    #
    @27
    @22
    @4
    @11
    @7
    df-ov
    @4
    cvv
    wcel
    @11
    cvv
    wcel
    @32
    @22
    wceq
    vx
    vex
    vy
    vex
    @4
    @11
    cF
    cvv
    cvv
    uncov
    mp2an
    eqtr3i
    eqeq1i
    @22
    @13
    eqcom
    bitri
    a1i
    anbi12d
    bitrd
    opabbidv
    3eqtr4a
    adantlr
    mpteq12dva
    vx
    vy
    vz
    @7
    df-cur
    syl6eqr
    eqtr2d
end

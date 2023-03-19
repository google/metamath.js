include "cotp.mm"
include "wcel.mm"
include "cop.mm"
include "cv.mm"
include "co.mm"
include "wa.mm"
include "coprab.mm"
include "df-ot.mm"
include "mppsval.mm"
include "eleq12i.mm"
include "cvv.mm"
include "cxp.mm"
include "oprabss.mm"
include "sseli.mm"
include "mpstssv.mm"
include "syl5eqelr.mm"
include "adantr.mm"
include "wb.mm"
include "opelxp.mm"
include "wceq.mm"
include "w3a.mm"
include "simp1.mm"
include "simp2.mm"
include "simp3.mm"
include "oteq123d.mm"
include "eleq1d.mm"
include "oveq12d.mm"
include "eleq12d.mm"
include "anbi12d.mm"
include "eloprabga.mm"
include "3expa.mm"
include "sylanb.mm"
include "sylbi.mm"
include "pm5.21nii.mm"
include "bitri.mm"

theorem elmpps
  let cA: class A
  let cC: class C
  let cD: class D
  let cP: class P
  let cT: class T
  let cH: class H
  let cJ: class J
  let va: setvar a
  let vd: setvar d
  let vh: setvar h
  let vt: setvar t
  let vx: setvar x
  assume mppsval.p: |- P = ( mPreSt ` T )
  assume mppsval.j: |- J = ( mPPSt ` T )
  assume mppsval.c: |- C = ( mCls ` T )


  assert |- ( <. D , H , A >. e. J <-> ( <. D , H , A >. e. P /\ A e. ( D C H ) ) )

  proof
    cD
    cH
    cA
    cotp
    #
    cJ
    wcel
    cD
    cH
    cop
    #
    cA
    cop
    #
    vd
    cv
    #
    vh
    cv
    #
    va
    cv
    #
    cotp
    #
    cP
    wcel
    #
    @5
    @3
    @4
    cC
    co
    #
    wcel
    #
    wa
    #
    vd
    vh
    va
    coprab
    #
    wcel
    #
    @0
    cP
    wcel
    #
    cA
    cD
    cH
    cC
    co
    #
    wcel
    #
    wa
    #
    @0
    @2
    cJ
    @11
    cD
    cH
    cA
    df-ot
    #
    cC
    cP
    cT
    vh
    cJ
    va
    vd
    mppsval.p
    mppsval.j
    mppsval.c
    mppsval
    eleq12i
    @12
    @2
    cvv
    cvv
    cxp
    #
    cvv
    cxp
    #
    wcel
    #
    @16
    @11
    @19
    @2
    @10
    vd
    vh
    va
    oprabss
    sseli
    @13
    @20
    @15
    @13
    @2
    @0
    @19
    @17
    cP
    @19
    @0
    cP
    cT
    mppsval.p
    mpstssv
    sseli
    syl5eqelr
    adantr
    @20
    @1
    @18
    wcel
    #
    cA
    cvv
    wcel
    #
    wa
    @12
    @16
    wb
    #
    @1
    cA
    @18
    cvv
    opelxp
    @21
    cD
    cvv
    wcel
    #
    cH
    cvv
    wcel
    #
    wa
    @22
    @23
    cD
    cH
    cvv
    cvv
    opelxp
    @24
    @25
    @22
    @23
    @10
    @16
    vd
    vh
    va
    cD
    cH
    cA
    cvv
    cvv
    cvv
    @3
    cD
    wceq
    #
    @4
    cH
    wceq
    #
    @5
    cA
    wceq
    #
    w3a
    #
    @7
    @13
    @9
    @15
    @29
    @6
    @0
    cP
    @29
    @3
    cD
    @4
    cH
    @5
    cA
    @26
    @27
    @28
    simp1
    #
    @26
    @27
    @28
    simp2
    #
    @26
    @27
    @28
    simp3
    #
    oteq123d
    eleq1d
    @29
    @5
    cA
    @8
    @14
    @32
    @29
    @3
    cD
    @4
    cH
    cC
    @30
    @31
    oveq12d
    eleq12d
    anbi12d
    eloprabga
    3expa
    sylanb
    sylbi
    pm5.21nii
    bitri
end

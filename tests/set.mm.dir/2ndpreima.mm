include "wss.mm"
include "c2nd.mm"
include "cxp.mm"
include "cres.mm"
include "ccnv.mm"
include "cima.mm"
include "cv.mm"
include "cfv.mm"
include "wcel.mm"
include "wa.mm"
include "cvv.mm"
include "c1st.mm"
include "ssel.mm"
include "pm4.71rd.mm"
include "anbi2d.mm"
include "wb.mm"
include "anass.mm"
include "bicomi.mm"
include "a1i.mm"
include "anbi1i.mm"
include "3bitrd.mm"
include "elxp7.mm"
include "syl6rbbr.mm"
include "ancom.mm"
include "3bitr3g.mm"
include "cin.mm"
include "cnvresima.mm"
include "eleq2i.mm"
include "elin.mm"
include "vex.mm"
include "wfo.mm"
include "wfn.mm"
include "fo2nd.mm"
include "fofn.mm"
include "elpreima.mm"
include "mp2b.mm"
include "mpbiran.mm"
include "3bitri.mm"
include "3bitr4g.mm"
include "eqrdv.mm"

theorem 2ndpreima
  let cA: class A
  let cB: class B
  let cC: class C
  let vw: setvar w


  assert |- ( A C_ C -> ( `' ( 2nd |` ( B X. C ) ) " A ) = ( B X. A ) )

  proof
    cA
    cC
    wss
    #
    vw
    c2nd
    cB
    cC
    cxp
    #
    cres
    ccnv
    cA
    cima
    #
    cB
    cA
    cxp
    #
    @0
    vw
    cv
    #
    c2nd
    cfv
    #
    cA
    wcel
    #
    @4
    @1
    wcel
    #
    wa
    #
    @4
    cvv
    cvv
    cxp
    wcel
    #
    @4
    c1st
    cfv
    cB
    wcel
    #
    @6
    wa
    wa
    #
    @4
    @2
    wcel
    #
    @4
    @3
    wcel
    @0
    @7
    @6
    wa
    #
    @9
    @10
    wa
    #
    @6
    wa
    #
    @8
    @11
    @0
    @15
    @9
    @10
    @5
    cC
    wcel
    #
    wa
    wa
    #
    @6
    wa
    #
    @13
    @0
    @15
    @14
    @16
    @6
    wa
    #
    wa
    #
    @14
    @16
    wa
    #
    @6
    wa
    #
    @18
    @0
    @6
    @19
    @14
    @0
    @6
    @16
    cA
    cC
    @5
    ssel
    pm4.71rd
    anbi2d
    @20
    @22
    wb
    @0
    @22
    @20
    @14
    @16
    @6
    anass
    bicomi
    a1i
    @22
    @18
    wb
    @0
    @21
    @17
    @6
    @9
    @10
    @16
    anass
    anbi1i
    a1i
    3bitrd
    @7
    @17
    @6
    @4
    cB
    cC
    elxp7
    anbi1i
    syl6rbbr
    @7
    @6
    ancom
    @9
    @10
    @6
    anass
    3bitr3g
    @12
    @4
    c2nd
    ccnv
    cA
    cima
    #
    @1
    cin
    #
    wcel
    @4
    @23
    wcel
    #
    @7
    wa
    @8
    @2
    @24
    @4
    @1
    cA
    c2nd
    cnvresima
    eleq2i
    @4
    @23
    @1
    elin
    @25
    @6
    @7
    @25
    @4
    cvv
    wcel
    #
    @6
    vw
    vex
    cvv
    cvv
    c2nd
    wfo
    c2nd
    cvv
    wfn
    @25
    @26
    @6
    wa
    wb
    fo2nd
    cvv
    cvv
    c2nd
    fofn
    cvv
    @4
    cA
    c2nd
    elpreima
    mp2b
    mpbiran
    anbi1i
    3bitri
    @4
    cB
    cA
    elxp7
    3bitr4g
    eqrdv
end

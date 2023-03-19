include "wss.mm"
include "c1st.mm"
include "cxp.mm"
include "cres.mm"
include "ccnv.mm"
include "cima.mm"
include "cv.mm"
include "cfv.mm"
include "wcel.mm"
include "wa.mm"
include "cvv.mm"
include "c2nd.mm"
include "wb.mm"
include "anass.mm"
include "a1i.mm"
include "ssel.mm"
include "pm4.71d.mm"
include "anbi1d.mm"
include "an12.mm"
include "anbi2i.mm"
include "3bitr4d.mm"
include "elxp7.mm"
include "syl6rbbr.mm"
include "syl6bb.mm"
include "cin.mm"
include "cnvresima.mm"
include "eleq2i.mm"
include "elin.mm"
include "vex.mm"
include "wfo.mm"
include "wfn.mm"
include "fo1st.mm"
include "fofn.mm"
include "elpreima.mm"
include "mp2b.mm"
include "mpbiran.mm"
include "anbi1i.mm"
include "3bitri.mm"
include "3bitr4g.mm"
include "eqrdv.mm"

theorem 1stpreima
  let cA: class A
  let cB: class B
  let cC: class C
  let vw: setvar w


  assert |- ( A C_ B -> ( `' ( 1st |` ( B X. C ) ) " A ) = ( A X. C ) )

  proof
    cA
    cB
    wss
    #
    vw
    c1st
    cB
    cC
    cxp
    #
    cres
    ccnv
    cA
    cima
    #
    cA
    cC
    cxp
    #
    @0
    vw
    cv
    #
    c1st
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
    @6
    @4
    c2nd
    cfv
    cC
    wcel
    #
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
    @8
    @6
    @9
    @10
    wa
    #
    wa
    #
    @11
    @0
    @14
    @6
    @9
    @5
    cB
    wcel
    #
    @10
    wa
    wa
    #
    wa
    #
    @8
    @0
    @6
    @15
    wa
    #
    @13
    wa
    #
    @6
    @15
    @13
    wa
    #
    wa
    #
    @14
    @17
    @19
    @21
    wb
    @0
    @6
    @15
    @13
    anass
    a1i
    @0
    @6
    @18
    @13
    @0
    @6
    @15
    cA
    cB
    @5
    ssel
    pm4.71d
    anbi1d
    @17
    @21
    wb
    @0
    @16
    @20
    @6
    @9
    @15
    @10
    an12
    anbi2i
    a1i
    3bitr4d
    @7
    @16
    @6
    @4
    cB
    cC
    elxp7
    anbi2i
    syl6rbbr
    @6
    @9
    @10
    an12
    syl6bb
    @12
    @4
    c1st
    ccnv
    cA
    cima
    #
    @1
    cin
    #
    wcel
    @4
    @22
    wcel
    #
    @7
    wa
    @8
    @2
    @23
    @4
    @1
    cA
    c1st
    cnvresima
    eleq2i
    @4
    @22
    @1
    elin
    @24
    @6
    @7
    @24
    @4
    cvv
    wcel
    #
    @6
    vw
    vex
    cvv
    cvv
    c1st
    wfo
    c1st
    cvv
    wfn
    @24
    @25
    @6
    wa
    wb
    fo1st
    cvv
    cvv
    c1st
    fofn
    cvv
    @4
    cA
    c1st
    elpreima
    mp2b
    mpbiran
    anbi1i
    3bitri
    @4
    cA
    cC
    elxp7
    3bitr4g
    eqrdv
end

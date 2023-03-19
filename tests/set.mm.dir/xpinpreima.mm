include "cv.mm"
include "c1st.mm"
include "cfv.mm"
include "wcel.mm"
include "cvv.mm"
include "cxp.mm"
include "crab.mm"
include "c2nd.mm"
include "cin.mm"
include "wa.mm"
include "cres.mm"
include "ccnv.mm"
include "cima.mm"
include "inrab.mm"
include "wf.mm"
include "wfn.mm"
include "wceq.mm"
include "f1stres.mm"
include "ffn.mm"
include "fncnvima2.mm"
include "mp2b.mm"
include "fvres.mm"
include "eleq1d.mm"
include "rabbiia.mm"
include "eqtri.mm"
include "f2ndres.mm"
include "ineq12i.mm"
include "xp2.mm"
include "3eqtr4ri.mm"

theorem xpinpreima
  let cA: class A
  let cB: class B
  let vr: setvar r


  assert |- ( A X. B ) = ( ( `' ( 1st |` ( _V X. _V ) ) " A ) i^i ( `' ( 2nd |` ( _V X. _V ) ) " B ) )

  proof
    vr
    cv
    #
    c1st
    cfv
    #
    cA
    wcel
    #
    vr
    cvv
    cvv
    cxp
    #
    crab
    #
    @0
    c2nd
    cfv
    #
    cB
    wcel
    #
    vr
    @3
    crab
    #
    cin
    @2
    @6
    wa
    vr
    @3
    crab
    c1st
    @3
    cres
    #
    ccnv
    cA
    cima
    #
    c2nd
    @3
    cres
    #
    ccnv
    cB
    cima
    #
    cin
    cA
    cB
    cxp
    @2
    @6
    vr
    @3
    inrab
    @9
    @4
    @11
    @7
    @9
    @0
    @8
    cfv
    #
    cA
    wcel
    #
    vr
    @3
    crab
    #
    @4
    @3
    cvv
    @8
    wf
    @8
    @3
    wfn
    @9
    @14
    wceq
    cvv
    cvv
    f1stres
    @3
    cvv
    @8
    ffn
    vr
    @3
    cA
    @8
    fncnvima2
    mp2b
    @13
    @2
    vr
    @3
    @0
    @3
    wcel
    #
    @12
    @1
    cA
    @0
    @3
    c1st
    fvres
    eleq1d
    rabbiia
    eqtri
    @11
    @0
    @10
    cfv
    #
    cB
    wcel
    #
    vr
    @3
    crab
    #
    @7
    @3
    cvv
    @10
    wf
    @10
    @3
    wfn
    @11
    @18
    wceq
    cvv
    cvv
    f2ndres
    @3
    cvv
    @10
    ffn
    vr
    @3
    cB
    @10
    fncnvima2
    mp2b
    @17
    @6
    vr
    @3
    @15
    @16
    @5
    cB
    @0
    @3
    c2nd
    fvres
    eleq1d
    rabbiia
    eqtri
    ineq12i
    vr
    cA
    cB
    xp2
    3eqtr4ri
end

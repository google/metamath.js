include "wss.mm"
include "wa.mm"
include "cxp.mm"
include "cv.mm"
include "c1st.mm"
include "cfv.mm"
include "wcel.mm"
include "crab.mm"
include "c2nd.mm"
include "cin.mm"
include "cres.mm"
include "ccnv.mm"
include "cima.mm"
include "cvv.mm"
include "xpss.mm"
include "rabss2.mm"
include "mp1i.mm"
include "simprl.mm"
include "simpll.mm"
include "simprrl.mm"
include "sseldd.mm"
include "simplr.mm"
include "simprrr.mm"
include "jca.mm"
include "elxp7.mm"
include "sylanbrc.mm"
include "rabss3d.mm"
include "eqssd.mm"
include "xp2.mm"
include "syl6reqr.mm"
include "inrab.mm"
include "syl6eqr.mm"
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

theorem xpinpreima2
  let cA: class A
  let cB: class B
  let cE: class E
  let cF: class F
  let vr: setvar r


  assert |- ( ( A C_ E /\ B C_ F ) -> ( A X. B ) = ( ( `' ( 1st |` ( E X. F ) ) " A ) i^i ( `' ( 2nd |` ( E X. F ) ) " B ) ) )

  proof
    cA
    cE
    wss
    #
    cB
    cF
    wss
    #
    wa
    #
    cA
    cB
    cxp
    #
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
    cE
    cF
    cxp
    #
    crab
    #
    @4
    c2nd
    cfv
    #
    cB
    wcel
    #
    vr
    @7
    crab
    #
    cin
    #
    c1st
    @7
    cres
    #
    ccnv
    cA
    cima
    #
    c2nd
    @7
    cres
    #
    ccnv
    cB
    cima
    #
    cin
    @2
    @3
    @6
    @10
    wa
    #
    vr
    @7
    crab
    #
    @12
    @2
    @18
    @17
    vr
    cvv
    cvv
    cxp
    #
    crab
    #
    @3
    @2
    @18
    @20
    @7
    @19
    wss
    @18
    @20
    wss
    @2
    cE
    cF
    xpss
    @17
    vr
    @7
    @19
    rabss2
    mp1i
    @2
    @17
    vr
    @19
    @7
    @2
    @4
    @19
    wcel
    #
    @17
    wa
    #
    wa
    #
    @21
    @5
    cE
    wcel
    #
    @9
    cF
    wcel
    #
    wa
    @4
    @7
    wcel
    #
    @2
    @21
    @17
    simprl
    @23
    @24
    @25
    @23
    cA
    cE
    @5
    @0
    @1
    @22
    simpll
    @2
    @21
    @6
    @10
    simprrl
    sseldd
    @23
    cB
    cF
    @9
    @0
    @1
    @22
    simplr
    @2
    @21
    @6
    @10
    simprrr
    sseldd
    jca
    @4
    cE
    cF
    elxp7
    sylanbrc
    rabss3d
    eqssd
    vr
    cA
    cB
    xp2
    syl6reqr
    @6
    @10
    vr
    @7
    inrab
    syl6eqr
    @14
    @8
    @16
    @11
    @14
    @4
    @13
    cfv
    #
    cA
    wcel
    #
    vr
    @7
    crab
    #
    @8
    @7
    cE
    @13
    wf
    @13
    @7
    wfn
    @14
    @29
    wceq
    cE
    cF
    f1stres
    @7
    cE
    @13
    ffn
    vr
    @7
    cA
    @13
    fncnvima2
    mp2b
    @28
    @6
    vr
    @7
    @26
    @27
    @5
    cA
    @4
    @7
    c1st
    fvres
    eleq1d
    rabbiia
    eqtri
    @16
    @4
    @15
    cfv
    #
    cB
    wcel
    #
    vr
    @7
    crab
    #
    @11
    @7
    cF
    @15
    wf
    @15
    @7
    wfn
    @16
    @32
    wceq
    cE
    cF
    f2ndres
    @7
    cF
    @15
    ffn
    vr
    @7
    cB
    @15
    fncnvima2
    mp2b
    @31
    @10
    vr
    @7
    @26
    @30
    @9
    cB
    @4
    @7
    c2nd
    fvres
    eleq1d
    rabbiia
    eqtri
    ineq12i
    syl6eqr
end

include "wfo.mm"
include "wfn.mm"
include "w3a.mm"
include "cv.mm"
include "ccom.mm"
include "cfv.mm"
include "wceq.mm"
include "wral.mm"
include "wcel.mm"
include "wa.mm"
include "wf.mm"
include "fof.mm"
include "3ad2ant1.mm"
include "fvco3.mm"
include "sylan.mm"
include "eqeq12d.mm"
include "ralbidva.mm"
include "wb.mm"
include "fveq2.mm"
include "cbvfo.mm"
include "bitrd.mm"
include "simp2.mm"
include "fnfco.mm"
include "syl2anc.mm"
include "simp3.mm"
include "eqfnfv.mm"
include "3bitr4d.mm"

theorem cocan2
  let cA: class A
  let cB: class B
  let cF: class F
  let cH: class H
  let cK: class K
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( F : A -onto-> B /\ H Fn B /\ K Fn B ) -> ( ( H o. F ) = ( K o. F ) <-> H = K ) )

  proof
    cA
    cB
    cF
    wfo
    #
    cH
    cB
    wfn
    #
    cK
    cB
    wfn
    #
    w3a
    #
    vy
    cv
    #
    cH
    cF
    ccom
    #
    cfv
    #
    @4
    cK
    cF
    ccom
    #
    cfv
    #
    wceq
    #
    vy
    cA
    wral
    #
    vx
    cv
    #
    cH
    cfv
    #
    @11
    cK
    cfv
    #
    wceq
    #
    vx
    cB
    wral
    #
    @5
    @7
    wceq
    #
    cH
    cK
    wceq
    #
    @3
    @10
    @4
    cF
    cfv
    #
    cH
    cfv
    #
    @18
    cK
    cfv
    #
    wceq
    #
    vy
    cA
    wral
    #
    @15
    @3
    @9
    @21
    vy
    cA
    @3
    @4
    cA
    wcel
    #
    wa
    @6
    @19
    @8
    @20
    @3
    cA
    cB
    cF
    wf
    #
    @23
    @6
    @19
    wceq
    @0
    @1
    @24
    @2
    cA
    cB
    cF
    fof
    3ad2ant1
    #
    cA
    cB
    @4
    cH
    cF
    fvco3
    sylan
    @3
    @24
    @23
    @8
    @20
    wceq
    @25
    cA
    cB
    @4
    cK
    cF
    fvco3
    sylan
    eqeq12d
    ralbidva
    @0
    @1
    @22
    @15
    wb
    @2
    @21
    @14
    vy
    vx
    cA
    cB
    cF
    @18
    @11
    wceq
    @19
    @12
    @20
    @13
    @18
    @11
    cH
    fveq2
    @18
    @11
    cK
    fveq2
    eqeq12d
    cbvfo
    3ad2ant1
    bitrd
    @3
    @5
    cA
    wfn
    #
    @7
    cA
    wfn
    #
    @16
    @10
    wb
    @3
    @1
    @24
    @26
    @0
    @1
    @2
    simp2
    #
    @25
    cB
    cA
    cH
    cF
    fnfco
    syl2anc
    @3
    @2
    @24
    @27
    @0
    @1
    @2
    simp3
    #
    @25
    cB
    cA
    cK
    cF
    fnfco
    syl2anc
    vy
    cA
    @5
    @7
    eqfnfv
    syl2anc
    @3
    @1
    @2
    @17
    @15
    wb
    @28
    @29
    vx
    cB
    cH
    cK
    eqfnfv
    syl2anc
    3bitr4d
end

include "wfo.mm"
include "wfn.mm"
include "w3a.mm"
include "ccom.mm"
include "wceq.mm"
include "wa.mm"
include "cv.mm"
include "cfv.mm"
include "wral.mm"
include "wcel.mm"
include "simplr.mm"
include "fveq1d.mm"
include "wf.mm"
include "simpl1.mm"
include "fof.mm"
include "syl.mm"
include "fvco3.mm"
include "sylan.mm"
include "3eqtr3d.mm"
include "ralrimiva.mm"
include "wb.mm"
include "fveq2.mm"
include "eqeq12d.mm"
include "cbvfo.mm"
include "mpbid.mm"
include "eqfnfv.mm"
include "3adant1.mm"
include "adantr.mm"
include "mpbird.mm"

theorem cocanfo
  let cA: class A
  let cB: class B
  let cF: class F
  let cG: class G
  let cH: class H
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( ( F : A -onto-> B /\ G Fn B /\ H Fn B ) /\ ( G o. F ) = ( H o. F ) ) -> G = H )

  proof
    cA
    cB
    cF
    wfo
    #
    cG
    cB
    wfn
    #
    cH
    cB
    wfn
    #
    w3a
    #
    cG
    cF
    ccom
    #
    cH
    cF
    ccom
    #
    wceq
    #
    wa
    #
    cG
    cH
    wceq
    #
    vx
    cv
    #
    cG
    cfv
    #
    @9
    cH
    cfv
    #
    wceq
    #
    vx
    cB
    wral
    #
    @7
    vy
    cv
    #
    cF
    cfv
    #
    cG
    cfv
    #
    @15
    cH
    cfv
    #
    wceq
    #
    vy
    cA
    wral
    #
    @13
    @7
    @18
    vy
    cA
    @7
    @14
    cA
    wcel
    #
    wa
    #
    @14
    @4
    cfv
    #
    @14
    @5
    cfv
    #
    @16
    @17
    @21
    @14
    @4
    @5
    @3
    @6
    @20
    simplr
    fveq1d
    @7
    cA
    cB
    cF
    wf
    #
    @20
    @22
    @16
    wceq
    @7
    @0
    @24
    @0
    @1
    @2
    @6
    simpl1
    #
    cA
    cB
    cF
    fof
    syl
    #
    cA
    cB
    @14
    cG
    cF
    fvco3
    sylan
    @7
    @24
    @20
    @23
    @17
    wceq
    @26
    cA
    cB
    @14
    cH
    cF
    fvco3
    sylan
    3eqtr3d
    ralrimiva
    @7
    @0
    @19
    @13
    wb
    @25
    @18
    @12
    vy
    vx
    cA
    cB
    cF
    @15
    @9
    wceq
    @16
    @10
    @17
    @11
    @15
    @9
    cG
    fveq2
    @15
    @9
    cH
    fveq2
    eqeq12d
    cbvfo
    syl
    mpbid
    @3
    @8
    @13
    wb
    #
    @6
    @1
    @2
    @27
    @0
    vx
    cB
    cG
    cH
    eqfnfv
    3adant1
    adantr
    mpbird
end

include "wf.mm"
include "ccom.mm"
include "wfo.mm"
include "wa.mm"
include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "wrex.mm"
include "wral.mm"
include "w3a.mm"
include "wcel.mm"
include "foelrn.mm"
include "ffvelrn.mm"
include "fvco3.mm"
include "fveq2.mm"
include "eqeq2d.mm"
include "rspcev.mm"
include "syl2anc.mm"
include "eqeq1.mm"
include "rexbidv.mm"
include "syl5ibrcom.mm"
include "rexlimdva.mm"
include "syl5.mm"
include "impl.mm"
include "ralrimiva.mm"
include "anim2i.mm"
include "3anass.mm"
include "dffo3.mm"
include "3imtr4i.mm"

theorem foco2
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F
  let cG: class G
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( ( F : B --> C /\ G : A --> B /\ ( F o. G ) : A -onto-> C ) -> F : B -onto-> C )

  proof
    cB
    cC
    cF
    wf
    #
    cA
    cB
    cG
    wf
    #
    cA
    cC
    cF
    cG
    ccom
    #
    wfo
    #
    wa
    #
    wa
    @0
    vy
    cv
    #
    vx
    cv
    #
    cF
    cfv
    #
    wceq
    #
    vx
    cB
    wrex
    #
    vy
    cC
    wral
    #
    wa
    @0
    @1
    @3
    w3a
    cB
    cC
    cF
    wfo
    @4
    @10
    @0
    @4
    @9
    vy
    cC
    @1
    @3
    @5
    cC
    wcel
    #
    @9
    @3
    @11
    wa
    @5
    vz
    cv
    #
    @2
    cfv
    #
    wceq
    #
    vz
    cA
    wrex
    @1
    @9
    vz
    cA
    cC
    @5
    @2
    foelrn
    @1
    @14
    @9
    vz
    cA
    @1
    @12
    cA
    wcel
    wa
    #
    @9
    @14
    @13
    @7
    wceq
    #
    vx
    cB
    wrex
    #
    @15
    @12
    cG
    cfv
    #
    cB
    wcel
    @13
    @18
    cF
    cfv
    #
    wceq
    #
    @17
    cA
    cB
    @12
    cG
    ffvelrn
    cA
    cB
    @12
    cF
    cG
    fvco3
    @16
    @20
    vx
    @18
    cB
    @6
    @18
    wceq
    @7
    @19
    @13
    @6
    @18
    cF
    fveq2
    eqeq2d
    rspcev
    syl2anc
    @14
    @8
    @16
    vx
    cB
    @5
    @13
    @7
    eqeq1
    rexbidv
    syl5ibrcom
    rexlimdva
    syl5
    impl
    ralrimiva
    anim2i
    @0
    @1
    @3
    3anass
    vx
    vy
    cB
    cC
    cF
    dffo3
    3imtr4i
end

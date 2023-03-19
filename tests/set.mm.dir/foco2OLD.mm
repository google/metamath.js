include "wf.mm"
include "ccom.mm"
include "wfo.mm"
include "w3a.mm"
include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "wrex.mm"
include "wral.mm"
include "simp1.mm"
include "wa.mm"
include "wcel.mm"
include "foelrn.mm"
include "ffvelrn.mm"
include "adantll.mm"
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
include "3impa.mm"
include "dffo3.mm"
include "sylanbrc.mm"

theorem foco2OLD
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
    w3a
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
    cB
    cC
    cF
    wfo
    @0
    @1
    @3
    simp1
    @0
    @1
    @3
    @9
    @0
    @1
    wa
    #
    @3
    wa
    @8
    vy
    cC
    @10
    @3
    @4
    cC
    wcel
    #
    @8
    @3
    @11
    wa
    @4
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
    @10
    @8
    vz
    cA
    cC
    @4
    @2
    foelrn
    @10
    @14
    @8
    vz
    cA
    @10
    @12
    cA
    wcel
    #
    wa
    #
    @8
    @14
    @13
    @6
    wceq
    #
    vx
    cB
    wrex
    #
    @16
    @12
    cG
    cfv
    #
    cB
    wcel
    #
    @13
    @19
    cF
    cfv
    #
    wceq
    #
    @18
    @1
    @15
    @20
    @0
    cA
    cB
    @12
    cG
    ffvelrn
    adantll
    @1
    @15
    @22
    @0
    cA
    cB
    @12
    cF
    cG
    fvco3
    adantll
    @17
    @22
    vx
    @19
    cB
    @5
    @19
    wceq
    @6
    @21
    @13
    @5
    @19
    cF
    fveq2
    eqeq2d
    rspcev
    syl2anc
    @14
    @7
    @17
    vx
    cB
    @4
    @13
    @6
    eqeq1
    rexbidv
    syl5ibrcom
    rexlimdva
    syl5
    impl
    ralrimiva
    3impa
    vx
    vy
    cB
    cC
    cF
    dffo3
    sylanbrc
end

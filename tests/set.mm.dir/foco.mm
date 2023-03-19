include "wfo.mm"
include "wa.mm"
include "ccom.mm"
include "wf.mm"
include "crn.mm"
include "wceq.mm"
include "dffo2.mm"
include "fco.mm"
include "ad2ant2r.mm"
include "cdm.mm"
include "fdm.mm"
include "eqtr3.mm"
include "sylan.mm"
include "rncoeq.mm"
include "eqeq1d.mm"
include "biimpar.mm"
include "an32s.mm"
include "adantrl.mm"
include "jca.mm"
include "syl2anb.mm"
include "sylibr.mm"

theorem foco
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F
  let cG: class G


  assert |- ( ( F : B -onto-> C /\ G : A -onto-> B ) -> ( F o. G ) : A -onto-> C )

  proof
    cB
    cC
    cF
    wfo
    #
    cA
    cB
    cG
    wfo
    #
    wa
    cA
    cC
    cF
    cG
    ccom
    #
    wf
    #
    @2
    crn
    #
    cC
    wceq
    #
    wa
    #
    cA
    cC
    @2
    wfo
    @0
    cB
    cC
    cF
    wf
    #
    cF
    crn
    #
    cC
    wceq
    #
    wa
    #
    cA
    cB
    cG
    wf
    #
    cG
    crn
    #
    cB
    wceq
    #
    wa
    #
    @6
    @1
    cB
    cC
    cF
    dffo2
    cA
    cB
    cG
    dffo2
    @10
    @14
    wa
    @3
    @5
    @7
    @11
    @3
    @9
    @13
    cA
    cB
    cC
    cF
    cG
    fco
    ad2ant2r
    @10
    @13
    @5
    @11
    @7
    @13
    @9
    @5
    @7
    @13
    wa
    cF
    cdm
    #
    @12
    wceq
    #
    @9
    @5
    @7
    @15
    cB
    wceq
    @13
    @16
    cB
    cC
    cF
    fdm
    @15
    @12
    cB
    eqtr3
    sylan
    @16
    @5
    @9
    @16
    @4
    @8
    cC
    cF
    cG
    rncoeq
    eqeq1d
    biimpar
    sylan
    an32s
    adantrl
    jca
    syl2anb
    cA
    cC
    @2
    dffo2
    sylibr
end

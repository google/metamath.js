include "wrel.mm"
include "cfn.mm"
include "wcel.mm"
include "cdm.mm"
include "crn.mm"
include "wa.mm"
include "dmfi.mm"
include "rnfi.mm"
include "jca.mm"
include "cxp.mm"
include "wss.mm"
include "xpfi.mm"
include "relssdmrn.mm"
include "ssfi.mm"
include "syl2anr.mm"
include "ex.mm"
include "impbid2.mm"

theorem relfi
  let cA: class A


  assert |- ( Rel A -> ( A e. Fin <-> ( dom A e. Fin /\ ran A e. Fin ) ) )

  proof
    cA
    wrel
    #
    cA
    cfn
    wcel
    #
    cA
    cdm
    #
    cfn
    wcel
    #
    cA
    crn
    #
    cfn
    wcel
    #
    wa
    #
    @1
    @3
    @5
    cA
    dmfi
    cA
    rnfi
    jca
    @0
    @6
    @1
    @6
    @2
    @4
    cxp
    #
    cfn
    wcel
    cA
    @7
    wss
    @1
    @0
    @2
    @4
    xpfi
    cA
    relssdmrn
    @7
    cA
    ssfi
    syl2anr
    ex
    impbid2
end

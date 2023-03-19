include "cxp.mm"
include "c0.mm"
include "wne.mm"
include "wss.mm"
include "wa.mm"
include "cdm.mm"
include "wceq.mm"
include "xpnz.mm"
include "dmxp.mm"
include "adantl.mm"
include "sylbir.mm"
include "adantr.mm"
include "dmss.mm"
include "eqsstr3d.mm"
include "dmxpss.mm"
include "syl6ss.mm"
include "crn.mm"
include "rnxp.mm"
include "rnss.mm"
include "rnxpss.mm"
include "jca.mm"
include "ex.mm"
include "xpss12.mm"
include "impbid1.mm"

theorem ssxpb
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D


  assert |- ( ( A X. B ) =/= (/) -> ( ( A X. B ) C_ ( C X. D ) <-> ( A C_ C /\ B C_ D ) ) )

  proof
    cA
    cB
    cxp
    #
    c0
    wne
    #
    @0
    cC
    cD
    cxp
    #
    wss
    #
    cA
    cC
    wss
    #
    cB
    cD
    wss
    #
    wa
    #
    @1
    @3
    @6
    @1
    @3
    wa
    #
    @4
    @5
    @7
    cA
    @2
    cdm
    #
    cC
    @7
    cA
    @0
    cdm
    #
    @8
    @1
    @9
    cA
    wceq
    #
    @3
    @1
    cA
    c0
    wne
    #
    cB
    c0
    wne
    #
    wa
    #
    @10
    cA
    cB
    xpnz
    #
    @12
    @10
    @11
    cA
    cB
    dmxp
    adantl
    sylbir
    adantr
    @3
    @9
    @8
    wss
    @1
    @0
    @2
    dmss
    adantl
    eqsstr3d
    cC
    cD
    dmxpss
    syl6ss
    @7
    cB
    @2
    crn
    #
    cD
    @7
    cB
    @0
    crn
    #
    @15
    @1
    @16
    cB
    wceq
    #
    @3
    @1
    @13
    @17
    @14
    @11
    @17
    @12
    cA
    cB
    rnxp
    adantr
    sylbir
    adantr
    @3
    @16
    @15
    wss
    @1
    @0
    @2
    rnss
    adantl
    eqsstr3d
    cC
    cD
    rnxpss
    syl6ss
    jca
    ex
    cA
    cC
    cB
    cD
    xpss12
    impbid1
end

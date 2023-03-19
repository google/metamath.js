include "wf.mm"
include "cin.mm"
include "c0.mm"
include "wceq.mm"
include "wa.mm"
include "ccnv.mm"
include "cdm.mm"
include "cima.mm"
include "wss.mm"
include "crn.mm"
include "df-rn.mm"
include "frn.mm"
include "adantr.mm"
include "syl5eqssr.mm"
include "ssdisj.mm"
include "sylancom.mm"
include "imadisj.mm"
include "sylibr.mm"

theorem fimacnvdisj
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F


  assert |- ( ( F : A --> B /\ ( B i^i C ) = (/) ) -> ( `' F " C ) = (/) )

  proof
    cA
    cB
    cF
    wf
    #
    cB
    cC
    cin
    c0
    wceq
    #
    wa
    #
    cF
    ccnv
    #
    cdm
    #
    cC
    cin
    c0
    wceq
    #
    @3
    cC
    cima
    c0
    wceq
    @0
    @1
    @4
    cB
    wss
    @5
    @2
    @4
    cF
    crn
    #
    cB
    cF
    df-rn
    @0
    @6
    cB
    wss
    @1
    cA
    cB
    cF
    frn
    adantr
    syl5eqssr
    @4
    cB
    cC
    ssdisj
    sylancom
    @3
    cC
    imadisj
    sylibr
end

include "wss.mm"
include "wpss.mm"
include "wceq.mm"
include "wo.mm"
include "sspss.mm"
include "wi.mm"
include "psstr.mm"
include "ex.mm"
include "psseq1.mm"
include "biimprd.mm"
include "jaoi.mm"
include "imp.mm"
include "sylanb.mm"

theorem sspsstr
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A C_ B /\ B C. C ) -> A C. C )

  proof
    cA
    cB
    wss
    cA
    cB
    wpss
    #
    cA
    cB
    wceq
    #
    wo
    #
    cB
    cC
    wpss
    #
    cA
    cC
    wpss
    #
    cA
    cB
    sspss
    @2
    @3
    @4
    @0
    @3
    @4
    wi
    @1
    @0
    @3
    @4
    cA
    cB
    cC
    psstr
    ex
    @1
    @4
    @3
    cA
    cB
    cC
    psseq1
    biimprd
    jaoi
    imp
    sylanb
end

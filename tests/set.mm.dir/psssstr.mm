include "wss.mm"
include "wpss.mm"
include "wceq.mm"
include "wo.mm"
include "sspss.mm"
include "psstr.mm"
include "ex.mm"
include "psseq2.mm"
include "biimpcd.mm"
include "jaod.mm"
include "imp.mm"
include "sylan2b.mm"

theorem psssstr
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A C. B /\ B C_ C ) -> A C. C )

  proof
    cB
    cC
    wss
    cA
    cB
    wpss
    #
    cB
    cC
    wpss
    #
    cB
    cC
    wceq
    #
    wo
    #
    cA
    cC
    wpss
    #
    cB
    cC
    sspss
    @0
    @3
    @4
    @0
    @1
    @4
    @2
    @0
    @1
    @4
    cA
    cB
    cC
    psstr
    ex
    @2
    @0
    @4
    cB
    cC
    cA
    psseq2
    biimpcd
    jaod
    imp
    sylan2b
end

include "wcel.mm"
include "wceq.mm"
include "wsbc.mm"
include "csb.mm"
include "sbceqg.mm"
include "csbconstg.mm"
include "eqeq1d.mm"
include "bitrd.mm"

theorem sbceq2g
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cV: class V

  disjoint B x
  assert |- ( A e. V -> ( [. A / x ]. B = C <-> B = [_ A / x ]_ C ) )

  proof
    cA
    cV
    wcel
    #
    cB
    cC
    wceq
    vx
    cA
    wsbc
    vx
    cA
    cB
    csb
    #
    vx
    cA
    cC
    csb
    #
    wceq
    cB
    @2
    wceq
    vx
    cA
    cB
    cC
    cV
    sbceqg
    @0
    @1
    cB
    @2
    vx
    cA
    cB
    cV
    csbconstg
    eqeq1d
    bitrd
end

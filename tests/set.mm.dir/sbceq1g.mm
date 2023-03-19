include "wcel.mm"
include "wceq.mm"
include "wsbc.mm"
include "csb.mm"
include "sbceqg.mm"
include "csbconstg.mm"
include "eqeq2d.mm"
include "bitrd.mm"

theorem sbceq1g
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cV: class V

  disjoint C x
  assert |- ( A e. V -> ( [. A / x ]. B = C <-> [_ A / x ]_ B = C ) )

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
    @1
    cC
    wceq
    vx
    cA
    cB
    cC
    cV
    sbceqg
    @0
    @2
    cC
    @1
    vx
    cA
    cC
    cV
    csbconstg
    eqeq2d
    bitrd
end

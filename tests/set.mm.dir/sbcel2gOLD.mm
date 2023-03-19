include "wcel.mm"
include "wsbc.mm"
include "csb.mm"
include "sbcel12.mm"
include "csbconstg.mm"
include "eleq1d.mm"
include "syl5bb.mm"

theorem sbcel2gOLD
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cV: class V

  disjoint B x
  assert |- ( A e. V -> ( [. A / x ]. B e. C <-> B e. [_ A / x ]_ C ) )

  proof
    cB
    cC
    wcel
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
    wcel
    cA
    cV
    wcel
    #
    cB
    @1
    wcel
    vx
    cA
    cB
    cC
    sbcel12
    @2
    @0
    cB
    @1
    vx
    cA
    cB
    cV
    csbconstg
    eleq1d
    syl5bb
end

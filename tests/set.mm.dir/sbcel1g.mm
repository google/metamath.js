include "wcel.mm"
include "wsbc.mm"
include "csb.mm"
include "sbcel12.mm"
include "csbconstg.mm"
include "eleq2d.mm"
include "syl5bb.mm"

theorem sbcel1g
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cV: class V

  disjoint C x
  assert |- ( A e. V -> ( [. A / x ]. B e. C <-> [_ A / x ]_ B e. C ) )

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
    @0
    cC
    wcel
    vx
    cA
    cB
    cC
    sbcel12
    @2
    @1
    cC
    @0
    vx
    cA
    cC
    cV
    csbconstg
    eleq2d
    syl5bb
end

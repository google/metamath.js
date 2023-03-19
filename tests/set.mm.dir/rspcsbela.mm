include "wcel.mm"
include "wral.mm"
include "csb.mm"
include "wsbc.mm"
include "rspsbc.mm"
include "sbcel1g.mm"
include "sylibd.mm"
include "imp.mm"

theorem rspcsbela
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D

  disjoint B x
  disjoint D x
  assert |- ( ( A e. B /\ A. x e. B C e. D ) -> [_ A / x ]_ C e. D )

  proof
    cA
    cB
    wcel
    #
    cC
    cD
    wcel
    #
    vx
    cB
    wral
    #
    vx
    cA
    cC
    csb
    cD
    wcel
    #
    @0
    @2
    @1
    vx
    cA
    wsbc
    @3
    @1
    vx
    cA
    cB
    rspsbc
    vx
    cA
    cC
    cD
    cB
    sbcel1g
    sylibd
    imp
end

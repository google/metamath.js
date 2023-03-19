include "cc.mm"
include "wcel.mm"
include "chil.mm"
include "w3a.mm"
include "cmul.mm"
include "co.mm"
include "csm.mm"
include "wceq.mm"
include "wa.mm"
include "mulcom.mm"
include "oveq1d.mm"
include "3adant3.mm"
include "ax-hvmulass.mm"
include "3com12.mm"
include "3eqtr3d.mm"

theorem hvmulcom
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A e. CC /\ B e. CC /\ C e. ~H ) -> ( A .h ( B .h C ) ) = ( B .h ( A .h C ) ) )

  proof
    cA
    cc
    wcel
    #
    cB
    cc
    wcel
    #
    cC
    chil
    wcel
    #
    w3a
    cA
    cB
    cmul
    co
    #
    cC
    csm
    co
    #
    cB
    cA
    cmul
    co
    #
    cC
    csm
    co
    #
    cA
    cB
    cC
    csm
    co
    csm
    co
    cB
    cA
    cC
    csm
    co
    csm
    co
    #
    @0
    @1
    @4
    @6
    wceq
    @2
    @0
    @1
    wa
    @3
    @5
    cC
    csm
    cA
    cB
    mulcom
    oveq1d
    3adant3
    cA
    cB
    cC
    ax-hvmulass
    @1
    @0
    @2
    @6
    @7
    wceq
    cB
    cA
    cC
    ax-hvmulass
    3com12
    3eqtr3d
end

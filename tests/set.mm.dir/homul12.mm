include "cc.mm"
include "wcel.mm"
include "chil.mm"
include "wf.mm"
include "w3a.mm"
include "cmul.mm"
include "co.mm"
include "chot.mm"
include "wceq.mm"
include "wa.mm"
include "mulcom.mm"
include "oveq1d.mm"
include "3adant3.mm"
include "homulass.mm"
include "3com12.mm"
include "3eqtr3d.mm"

theorem homul12
  let cA: class A
  let cB: class B
  let cT: class T


  assert |- ( ( A e. CC /\ B e. CC /\ T : ~H --> ~H ) -> ( A .op ( B .op T ) ) = ( B .op ( A .op T ) ) )

  proof
    cA
    cc
    wcel
    #
    cB
    cc
    wcel
    #
    chil
    chil
    cT
    wf
    #
    w3a
    cA
    cB
    cmul
    co
    #
    cT
    chot
    co
    #
    cB
    cA
    cmul
    co
    #
    cT
    chot
    co
    #
    cA
    cB
    cT
    chot
    co
    chot
    co
    cB
    cA
    cT
    chot
    co
    chot
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
    cT
    chot
    cA
    cB
    mulcom
    oveq1d
    3adant3
    cA
    cB
    cT
    homulass
    @1
    @0
    @2
    @6
    @7
    wceq
    cB
    cA
    cT
    homulass
    3com12
    3eqtr3d
end

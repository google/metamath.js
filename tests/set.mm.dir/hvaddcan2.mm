include "chil.mm"
include "wcel.mm"
include "cva.mm"
include "co.mm"
include "wceq.mm"
include "wb.mm"
include "w3a.mm"
include "ax-hvcom.mm"
include "3adant3.mm"
include "3adant2.mm"
include "eqeq12d.mm"
include "hvaddcan.mm"
include "bitr3d.mm"
include "3coml.mm"

theorem hvaddcan2
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A e. ~H /\ B e. ~H /\ C e. ~H ) -> ( ( A +h C ) = ( B +h C ) <-> A = B ) )

  proof
    cC
    chil
    wcel
    #
    cA
    chil
    wcel
    #
    cB
    chil
    wcel
    #
    cA
    cC
    cva
    co
    #
    cB
    cC
    cva
    co
    #
    wceq
    #
    cA
    cB
    wceq
    #
    wb
    @0
    @1
    @2
    w3a
    #
    cC
    cA
    cva
    co
    #
    cC
    cB
    cva
    co
    #
    wceq
    @5
    @6
    @7
    @8
    @3
    @9
    @4
    @0
    @1
    @8
    @3
    wceq
    @2
    cC
    cA
    ax-hvcom
    3adant3
    @0
    @2
    @9
    @4
    wceq
    @1
    cC
    cB
    ax-hvcom
    3adant2
    eqeq12d
    cC
    cA
    cB
    hvaddcan
    bitr3d
    3coml
end

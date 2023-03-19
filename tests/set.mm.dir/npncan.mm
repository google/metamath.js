include "cc.mm"
include "wcel.mm"
include "w3a.mm"
include "cmin.mm"
include "co.mm"
include "caddc.mm"
include "wceq.mm"
include "subcl.mm"
include "3adant3.mm"
include "addsubass.mm"
include "syld3an1.mm"
include "wa.mm"
include "npcan.mm"
include "oveq1d.mm"
include "eqtr3d.mm"

theorem npncan
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A e. CC /\ B e. CC /\ C e. CC ) -> ( ( A - B ) + ( B - C ) ) = ( A - C ) )

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
    cc
    wcel
    #
    w3a
    cA
    cB
    cmin
    co
    #
    cB
    caddc
    co
    #
    cC
    cmin
    co
    #
    @3
    cB
    cC
    cmin
    co
    caddc
    co
    #
    cA
    cC
    cmin
    co
    #
    @3
    cc
    wcel
    #
    @1
    @0
    @2
    @5
    @6
    wceq
    @0
    @1
    @8
    @2
    cA
    cB
    subcl
    3adant3
    @3
    cB
    cC
    addsubass
    syld3an1
    @0
    @1
    @5
    @7
    wceq
    @2
    @0
    @1
    wa
    @4
    cA
    cC
    cmin
    cA
    cB
    npcan
    oveq1d
    3adant3
    eqtr3d
end

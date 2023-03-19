include "cc.mm"
include "wcel.mm"
include "w3a.mm"
include "cmin.mm"
include "co.mm"
include "caddc.mm"
include "subcl.mm"
include "3adant3.mm"
include "simp3.mm"
include "simp2.mm"
include "addassd.mm"
include "nppcan.mm"
include "eqtr3d.mm"

theorem nppcan3
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A e. CC /\ B e. CC /\ C e. CC ) -> ( ( A - B ) + ( C + B ) ) = ( A + C ) )

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
    #
    cA
    cB
    cmin
    co
    #
    cC
    caddc
    co
    cB
    caddc
    co
    @4
    cC
    cB
    caddc
    co
    caddc
    co
    cA
    cC
    caddc
    co
    @3
    @4
    cC
    cB
    @0
    @1
    @4
    cc
    wcel
    @2
    cA
    cB
    subcl
    3adant3
    @0
    @1
    @2
    simp3
    @0
    @1
    @2
    simp2
    addassd
    cA
    cB
    cC
    nppcan
    eqtr3d
end

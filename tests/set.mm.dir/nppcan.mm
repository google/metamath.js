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
include "add32d.mm"
include "wceq.mm"
include "wa.mm"
include "npcan.mm"
include "oveq1d.mm"
include "eqtrd.mm"

theorem nppcan
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A e. CC /\ B e. CC /\ C e. CC ) -> ( ( ( A - B ) + C ) + B ) = ( A + C ) )

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
    cB
    caddc
    co
    #
    cC
    caddc
    co
    #
    cA
    cC
    caddc
    co
    #
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
    add32d
    @0
    @1
    @6
    @7
    wceq
    @2
    @0
    @1
    wa
    @5
    cA
    cC
    caddc
    cA
    cB
    npcan
    oveq1d
    3adant3
    eqtrd
end

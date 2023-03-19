include "cc.mm"
include "wcel.mm"
include "w3a.mm"
include "cmin.mm"
include "co.mm"
include "wceq.mm"
include "caddc.mm"
include "subadd.mm"
include "simp2.mm"
include "simp3.mm"
include "addcomd.mm"
include "eqeq1d.mm"
include "bitrd.mm"

theorem subadd2
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A e. CC /\ B e. CC /\ C e. CC ) -> ( ( A - B ) = C <-> ( C + B ) = A ) )

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
    cC
    wceq
    cB
    cC
    caddc
    co
    #
    cA
    wceq
    cC
    cB
    caddc
    co
    #
    cA
    wceq
    cA
    cB
    cC
    subadd
    @3
    @4
    @5
    cA
    @3
    cB
    cC
    @0
    @1
    @2
    simp2
    @0
    @1
    @2
    simp3
    addcomd
    eqeq1d
    bitrd
end

include "cc.mm"
include "wcel.mm"
include "w3a.mm"
include "caddc.mm"
include "co.mm"
include "wceq.mm"
include "cmin.mm"
include "simp2.mm"
include "simp1.mm"
include "addcomd.mm"
include "eqeq1d.mm"
include "wb.mm"
include "simp3.mm"
include "addsubeq4.mm"
include "syl22anc.mm"
include "addcan.mm"
include "3bitr3d.mm"

theorem subcan
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A e. CC /\ B e. CC /\ C e. CC ) -> ( ( A - B ) = ( A - C ) <-> B = C ) )

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
    cB
    cA
    caddc
    co
    #
    cA
    cC
    caddc
    co
    #
    wceq
    #
    cA
    cB
    caddc
    co
    #
    @5
    wceq
    cA
    cB
    cmin
    co
    cA
    cC
    cmin
    co
    wceq
    #
    cB
    cC
    wceq
    @3
    @4
    @7
    @5
    @3
    cB
    cA
    @0
    @1
    @2
    simp2
    #
    @0
    @1
    @2
    simp1
    #
    addcomd
    eqeq1d
    @3
    @1
    @0
    @0
    @2
    @6
    @8
    wb
    @9
    @10
    @10
    @0
    @1
    @2
    simp3
    cB
    cA
    cA
    cC
    addsubeq4
    syl22anc
    cA
    cB
    cC
    addcan
    3bitr3d
end

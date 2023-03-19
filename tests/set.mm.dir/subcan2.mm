include "cc.mm"
include "wcel.mm"
include "w3a.mm"
include "cmin.mm"
include "co.mm"
include "wceq.mm"
include "caddc.mm"
include "wb.mm"
include "simp1.mm"
include "simp3.mm"
include "subcl.mm"
include "3adant1.mm"
include "subadd2.mm"
include "syl3anc.mm"
include "npcan.mm"
include "eqeq1d.mm"
include "eqcom.mm"
include "syl6bb.mm"
include "bitrd.mm"

theorem subcan2
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A e. CC /\ B e. CC /\ C e. CC ) -> ( ( A - C ) = ( B - C ) <-> A = B ) )

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
    cC
    cmin
    co
    cB
    cC
    cmin
    co
    #
    wceq
    #
    @4
    cC
    caddc
    co
    #
    cA
    wceq
    #
    cA
    cB
    wceq
    #
    @3
    @0
    @2
    @4
    cc
    wcel
    #
    @5
    @7
    wb
    @0
    @1
    @2
    simp1
    @0
    @1
    @2
    simp3
    @1
    @2
    @9
    @0
    cB
    cC
    subcl
    3adant1
    cA
    cC
    @4
    subadd2
    syl3anc
    @3
    @7
    cB
    cA
    wceq
    @8
    @3
    @6
    cB
    cA
    @1
    @2
    @6
    cB
    wceq
    @0
    cB
    cC
    npcan
    3adant1
    eqeq1d
    cB
    cA
    eqcom
    syl6bb
    bitrd
end

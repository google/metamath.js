include "cgru.mm"
include "wcel.mm"
include "w3a.mm"
include "cop.mm"
include "csn.mm"
include "cpr.mm"
include "wceq.mm"
include "dfopg.mm"
include "3adant1.mm"
include "simp1.mm"
include "grusn.mm"
include "3adant3.mm"
include "grupr.mm"
include "syl3anc.mm"
include "eqeltrd.mm"

theorem gruop
  let cA: class A
  let cB: class B
  let cU: class U
  let vx: setvar x
  let vy: setvar y
  let cF: class F


  assert |- ( ( U e. Univ /\ A e. U /\ B e. U ) -> <. A , B >. e. U )

  proof
    cU
    cgru
    wcel
    #
    cA
    cU
    wcel
    #
    cB
    cU
    wcel
    #
    w3a
    #
    cA
    cB
    cop
    #
    cA
    csn
    #
    cA
    cB
    cpr
    #
    cpr
    #
    cU
    @1
    @2
    @4
    @7
    wceq
    @0
    cA
    cB
    cU
    cU
    dfopg
    3adant1
    @3
    @0
    @5
    cU
    wcel
    #
    @6
    cU
    wcel
    @7
    cU
    wcel
    @0
    @1
    @2
    simp1
    @0
    @1
    @8
    @2
    cA
    cU
    grusn
    3adant3
    cA
    cB
    cU
    grupr
    @5
    @6
    cU
    grupr
    syl3anc
    eqeltrd
end

include "cgru.mm"
include "wcel.mm"
include "w3a.mm"
include "cun.mm"
include "cpr.mm"
include "cv.mm"
include "ciun.mm"
include "cuni.mm"
include "uniiun.mm"
include "wceq.mm"
include "uniprg.mm"
include "3adant1.mm"
include "syl5reqr.mm"
include "wral.mm"
include "simp1.mm"
include "grupr.mm"
include "wa.mm"
include "wo.mm"
include "vex.mm"
include "elpr.mm"
include "eleq1a.mm"
include "jaao.mm"
include "syl5bi.mm"
include "ralrimiv.mm"
include "gruiun.mm"
include "syl3anc.mm"
include "eqeltrd.mm"

theorem gruun
  let cA: class A
  let cB: class B
  let cU: class U
  let vx: setvar x
  let vy: setvar y
  let cF: class F


  assert |- ( ( U e. Univ /\ A e. U /\ B e. U ) -> ( A u. B ) e. U )

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
    cun
    #
    vx
    cA
    cB
    cpr
    #
    vx
    cv
    #
    ciun
    #
    cU
    @3
    @7
    @5
    cuni
    #
    @4
    vx
    @5
    uniiun
    @1
    @2
    @8
    @4
    wceq
    @0
    cA
    cB
    cU
    cU
    uniprg
    3adant1
    syl5reqr
    @3
    @0
    @5
    cU
    wcel
    @6
    cU
    wcel
    #
    vx
    @5
    wral
    #
    @7
    cU
    wcel
    @0
    @1
    @2
    simp1
    cA
    cB
    cU
    grupr
    @1
    @2
    @10
    @0
    @1
    @2
    wa
    #
    @9
    vx
    @5
    @6
    @5
    wcel
    @6
    cA
    wceq
    #
    @6
    cB
    wceq
    #
    wo
    @11
    @9
    @6
    cA
    cB
    vx
    vex
    elpr
    @1
    @12
    @9
    @2
    @13
    cA
    cU
    @6
    eleq1a
    cB
    cU
    @6
    eleq1a
    jaao
    syl5bi
    ralrimiv
    3adant1
    vx
    @5
    @6
    cU
    gruiun
    syl3anc
    eqeltrd
end

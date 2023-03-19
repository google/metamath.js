include "cgru.mm"
include "wcel.mm"
include "wa.mm"
include "csn.mm"
include "cpr.mm"
include "dfsn2.mm"
include "grupr.mm"
include "3anidm23.mm"
include "syl5eqel.mm"

theorem grusn
  let cA: class A
  let cU: class U
  let vx: setvar x
  let vy: setvar y
  let cB: class B
  let cF: class F


  assert |- ( ( U e. Univ /\ A e. U ) -> { A } e. U )

  proof
    cU
    cgru
    wcel
    #
    cA
    cU
    wcel
    #
    wa
    cA
    csn
    cA
    cA
    cpr
    #
    cU
    cA
    dfsn2
    @0
    @1
    @2
    cU
    wcel
    cA
    cA
    cU
    grupr
    3anidm23
    syl5eqel
end

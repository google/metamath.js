include "cgru.mm"
include "wcel.mm"
include "wf.mm"
include "w3a.mm"
include "crn.mm"
include "cuni.mm"
include "cpw.mm"
include "wss.mm"
include "simp1.mm"
include "gruurn.mm"
include "grupw.mm"
include "syl2anc.mm"
include "pwuni.mm"
include "a1i.mm"
include "gruss.mm"
include "syl3anc.mm"

theorem grurn
  let cA: class A
  let cU: class U
  let cF: class F
  let vx: setvar x
  let vy: setvar y
  let cB: class B


  assert |- ( ( U e. Univ /\ A e. U /\ F : A --> U ) -> ran F e. U )

  proof
    cU
    cgru
    wcel
    #
    cA
    cU
    wcel
    #
    cA
    cU
    cF
    wf
    #
    w3a
    #
    @0
    cF
    crn
    #
    cuni
    #
    cpw
    #
    cU
    wcel
    #
    @4
    @6
    wss
    #
    @4
    cU
    wcel
    @0
    @1
    @2
    simp1
    #
    @3
    @0
    @5
    cU
    wcel
    @7
    @9
    cA
    cU
    cF
    gruurn
    @5
    cU
    grupw
    syl2anc
    @8
    @3
    @4
    pwuni
    a1i
    @6
    @4
    cU
    gruss
    syl3anc
end

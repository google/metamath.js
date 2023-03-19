include "wcel.mm"
include "w3a.mm"
include "cv.mm"
include "wceq.mm"
include "ctp.mm"
include "cin.mm"
include "c0.mm"
include "wne.mm"
include "simp3.mm"
include "eleq2.mm"
include "syl5ibrcom.mm"
include "tpid3g.mm"
include "3ad2ant3.mm"
include "inelcm.mm"
include "sylan2.mm"
include "expcom.mm"
include "syld.mm"

theorem en3lplem1
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C

  disjoint A x
  disjoint B x
  disjoint C x
  assert |- ( ( A e. B /\ B e. C /\ C e. A ) -> ( x = A -> ( x i^i { A , B , C } ) =/= (/) ) )

  proof
    cA
    cB
    wcel
    #
    cB
    cC
    wcel
    #
    cC
    cA
    wcel
    #
    w3a
    #
    vx
    cv
    #
    cA
    wceq
    #
    cC
    @4
    wcel
    #
    @4
    cA
    cB
    cC
    ctp
    #
    cin
    c0
    wne
    #
    @3
    @6
    @5
    @2
    @0
    @1
    @2
    simp3
    @4
    cA
    cC
    eleq2
    syl5ibrcom
    @6
    @3
    @8
    @3
    @6
    cC
    @7
    wcel
    #
    @8
    @2
    @0
    @9
    @1
    cC
    cA
    cA
    cB
    tpid3g
    3ad2ant3
    cC
    @4
    @7
    inelcm
    sylan2
    expcom
    syld
end

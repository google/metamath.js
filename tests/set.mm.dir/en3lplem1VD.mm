include "wcel.mm"
include "w3a.mm"
include "cv.mm"
include "wceq.mm"
include "ctp.mm"
include "wa.mm"
include "wex.mm"
include "wi.mm"
include "idn1.mm"
include "simp3.mm"
include "e1a.mm"
include "tpid3g.mm"
include "idn2.mm"
include "eleq2.mm"
include "biimprd.mm"
include "e21.mm"
include "pm3.2.mm"
include "e12.mm"
include "elex22.mm"
include "e2.mm"
include "in2.mm"
include "in1.mm"

theorem en3lplem1VD
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B x
  disjoint B y
  disjoint C x
  disjoint C y
  assert |- ( ( A e. B /\ B e. C /\ C e. A ) -> ( x = A -> E. y ( y e. { A , B , C } /\ y e. x ) ) )

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
    vy
    cv
    #
    cA
    cB
    cC
    ctp
    #
    wcel
    @6
    @4
    wcel
    wa
    vy
    wex
    #
    wi
    @3
    @5
    @8
    @3
    @5
    cC
    @7
    wcel
    #
    cC
    @4
    wcel
    #
    wa
    #
    @8
    @3
    @9
    @5
    @10
    @11
    @3
    @2
    @9
    @3
    @3
    @2
    @3
    idn1
    @0
    @1
    @2
    simp3
    e1a
    #
    cC
    cA
    cA
    cB
    tpid3g
    e1a
    @3
    @5
    @5
    @2
    @10
    @3
    @5
    idn2
    @12
    @5
    @10
    @2
    @4
    cA
    cC
    eleq2
    biimprd
    e21
    @9
    @10
    pm3.2
    e12
    vy
    cC
    @7
    @4
    elex22
    e2
    in2
    in1
end

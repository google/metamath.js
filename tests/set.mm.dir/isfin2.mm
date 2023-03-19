include "cv.mm"
include "c0.mm"
include "wne.mm"
include "crpss.mm"
include "wor.mm"
include "wa.mm"
include "cuni.mm"
include "wcel.mm"
include "wi.mm"
include "cpw.mm"
include "wral.mm"
include "cfin2.mm"
include "wceq.mm"
include "pweq.mm"
include "pweqd.mm"
include "raleqdv.mm"
include "df-fin2.mm"
include "elab2g.mm"

theorem isfin2
  let vy: setvar y
  let cA: class A
  let cV: class V
  let vx: setvar x
  let cB: class B
  let cX: class X

  disjoint A y
  disjoint x y
  disjoint A x
  disjoint B y
  disjoint X x
  assert |- ( A e. V -> ( A e. Fin2 <-> A. y e. ~P ~P A ( ( y =/= (/) /\ [C.] Or y ) -> U. y e. y ) ) )

  proof
    vy
    cv
    #
    c0
    wne
    @0
    crpss
    wor
    wa
    @0
    cuni
    @0
    wcel
    wi
    #
    vy
    vx
    cv
    #
    cpw
    #
    cpw
    #
    wral
    @1
    vy
    cA
    cpw
    #
    cpw
    #
    wral
    vx
    cA
    cfin2
    cV
    @2
    cA
    wceq
    #
    @1
    vy
    @4
    @6
    @7
    @3
    @5
    @2
    cA
    pweq
    pweqd
    raleqdv
    vx
    vy
    df-fin2
    elab2g
end

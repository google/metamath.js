include "cv.mm"
include "wtr.mm"
include "c0.mm"
include "wne.mm"
include "cuni.mm"
include "wcel.mm"
include "cpw.mm"
include "cpr.mm"
include "wral.mm"
include "w3a.mm"
include "cwun.mm"
include "wceq.mm"
include "treq.mm"
include "neeq1.mm"
include "eleq2.mm"
include "raleqbi1dv.mm"
include "3anbi123d.mm"
include "df-wun.mm"
include "elab2g.mm"

theorem iswun
  let vx: setvar x
  let vy: setvar y
  let cU: class U
  let cV: class V
  let cA: class A
  let cB: class B
  let vu: setvar u

  disjoint x y
  disjoint U x
  disjoint U y
  disjoint A x
  disjoint A y
  disjoint B y
  disjoint u x
  disjoint u y
  disjoint U u
  assert |- ( U e. V -> ( U e. WUni <-> ( Tr U /\ U =/= (/) /\ A. x e. U ( U. x e. U /\ ~P x e. U /\ A. y e. U { x , y } e. U ) ) ) )

  proof
    vu
    cv
    #
    wtr
    #
    @0
    c0
    wne
    #
    vx
    cv
    #
    cuni
    #
    @0
    wcel
    #
    @3
    cpw
    #
    @0
    wcel
    #
    @3
    vy
    cv
    cpr
    #
    @0
    wcel
    #
    vy
    @0
    wral
    #
    w3a
    #
    vx
    @0
    wral
    #
    w3a
    cU
    wtr
    #
    cU
    c0
    wne
    #
    @4
    cU
    wcel
    #
    @6
    cU
    wcel
    #
    @8
    cU
    wcel
    #
    vy
    cU
    wral
    #
    w3a
    #
    vx
    cU
    wral
    #
    w3a
    vu
    cU
    cwun
    cV
    @0
    cU
    wceq
    #
    @1
    @13
    @2
    @14
    @12
    @20
    @0
    cU
    treq
    @0
    cU
    c0
    neeq1
    @11
    @19
    vx
    @0
    cU
    @21
    @5
    @15
    @7
    @16
    @10
    @18
    @0
    cU
    @4
    eleq2
    @0
    cU
    @6
    eleq2
    @9
    @17
    vy
    @0
    cU
    @0
    cU
    @8
    eleq2
    raleqbi1dv
    3anbi123d
    raleqbi1dv
    3anbi123d
    vx
    vy
    vu
    df-wun
    elab2g
end

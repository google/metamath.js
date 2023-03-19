include "wcel.mm"
include "cv.mm"
include "wss.mm"
include "crab.mm"
include "wral.mm"
include "cuni.mm"
include "wceq.mm"
include "ssid.mm"
include "sseq1.mm"
include "elrab3.mm"
include "mpbiri.mm"
include "elrab.mm"
include "simprbi.mm"
include "rgen.mm"
include "wa.mm"
include "ssunieq.mm"
include "eqcomd.mm"
include "sylancl.mm"

theorem unimax
  let vx: setvar x
  let cA: class A
  let cB: class B
  let vy: setvar y

  disjoint A x
  disjoint B x
  disjoint x y
  disjoint A y
  disjoint B y
  assert |- ( A e. B -> U. { x e. B | x C_ A } = A )

  proof
    cA
    cB
    wcel
    #
    cA
    vx
    cv
    #
    cA
    wss
    #
    vx
    cB
    crab
    #
    wcel
    #
    vy
    cv
    #
    cA
    wss
    #
    vy
    @3
    wral
    #
    @3
    cuni
    #
    cA
    wceq
    @0
    @4
    cA
    cA
    wss
    #
    cA
    ssid
    @2
    @9
    vx
    cA
    cB
    @1
    cA
    cA
    sseq1
    elrab3
    mpbiri
    @6
    vy
    @3
    @5
    @3
    wcel
    @5
    cB
    wcel
    @6
    @2
    @6
    vx
    @5
    cB
    @1
    @5
    cA
    sseq1
    elrab
    simprbi
    rgen
    @4
    @7
    wa
    cA
    @8
    vy
    cA
    @3
    ssunieq
    eqcomd
    sylancl
end

include "cv.mm"
include "wss.mm"
include "cin.mm"
include "cvv.mm"
include "vex.mm"
include "inex1.mm"
include "sseq2.mm"
include "wa.mm"
include "ssin.mm"
include "biimpi.mm"
include "cllem0.mm"

theorem superficl
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  assume superficl.a: |- A = { z | B C_ z }

  disjoint x y
  disjoint x z
  disjoint y z
  disjoint A y
  disjoint B z
  assert |- A. x e. A A. y e. A ( x i^i y ) e. A

  proof
    cB
    vz
    cv
    #
    wss
    cB
    vx
    cv
    #
    vy
    cv
    #
    cin
    #
    wss
    #
    cB
    @1
    wss
    #
    cB
    @2
    wss
    #
    vx
    vy
    vz
    @3
    cvv
    cA
    superficl.a
    @1
    @2
    vx
    vex
    inex1
    @0
    @3
    cB
    sseq2
    @0
    @1
    cB
    sseq2
    @0
    @2
    cB
    sseq2
    @5
    @6
    wa
    @4
    cB
    @1
    @2
    ssin
    biimpi
    cllem0
end

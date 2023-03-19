include "cv.mm"
include "ccom.mm"
include "wss.mm"
include "cin.mm"
include "cvv.mm"
include "vex.mm"
include "inex1.mm"
include "wceq.mm"
include "id.mm"
include "coeq12d.mm"
include "sseq12d.mm"
include "weq.mm"
include "trin2.mm"
include "cllem0.mm"

theorem trficl
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  assume trficl.a: |- A = { z | ( z o. z ) C_ z }

  disjoint x y
  disjoint x z
  disjoint y z
  disjoint A y
  assert |- A. x e. A A. y e. A ( x i^i y ) e. A

  proof
    vz
    cv
    #
    @0
    ccom
    #
    @0
    wss
    vx
    cv
    #
    vy
    cv
    #
    cin
    #
    @4
    ccom
    #
    @4
    wss
    @2
    @2
    ccom
    #
    @2
    wss
    @3
    @3
    ccom
    #
    @3
    wss
    vx
    vy
    vz
    @4
    cvv
    cA
    trficl.a
    @2
    @3
    vx
    vex
    inex1
    @0
    @4
    wceq
    #
    @1
    @5
    @0
    @4
    @8
    @0
    @4
    @0
    @4
    @8
    id
    #
    @9
    coeq12d
    @9
    sseq12d
    vz
    vx
    weq
    #
    @1
    @6
    @0
    @2
    @10
    @0
    @2
    @0
    @2
    @10
    id
    #
    @11
    coeq12d
    @11
    sseq12d
    vz
    vy
    weq
    #
    @1
    @7
    @0
    @3
    @12
    @0
    @3
    @0
    @3
    @12
    id
    #
    @13
    coeq12d
    @13
    sseq12d
    @2
    @3
    trin2
    cllem0
end

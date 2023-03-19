include "cv.mm"
include "wcel.mm"
include "wsb.mm"
include "wal.mm"
include "hbsb.mm"
include "bj-clelsb3.mm"
include "albii.mm"
include "3imtr3i.mm"

theorem bj-hblem
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  assume bj-hblem.1: |- ( y e. A -> A. x y e. A )

  disjoint A y
  disjoint x z
  assert |- ( z e. A -> A. x z e. A )

  proof
    vy
    cv
    cA
    wcel
    #
    vy
    vz
    wsb
    #
    @1
    vx
    wal
    vz
    cv
    cA
    wcel
    #
    @2
    vx
    wal
    @0
    vy
    vz
    vx
    bj-hblem.1
    hbsb
    vz
    vy
    cA
    bj-clelsb3
    #
    @1
    @2
    vx
    @3
    albii
    3imtr3i
end

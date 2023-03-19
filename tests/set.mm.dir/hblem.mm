include "cv.mm"
include "wcel.mm"
include "wsb.mm"
include "wal.mm"
include "hbsb.mm"
include "clelsb3.mm"
include "albii.mm"
include "3imtr3i.mm"

theorem hblem
  param vx: setvar x
  param vy: setvar y
  param vz: setvar z
  param cA: class A
  assume hblem.1: |- ( y e. A -> A. x y e. A )

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
    hblem.1
    hbsb
    vz
    vy
    cA
    clelsb3
    #
    @1
    @2
    vx
    @3
    albii
    3imtr3i
end

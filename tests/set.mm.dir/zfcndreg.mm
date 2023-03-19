include "cv.mm"
include "wcel.mm"
include "wn.mm"
include "wi.mm"
include "wal.mm"
include "wa.mm"
include "wex.mm"
include "nfe1.mm"
include "axregnd.mm"
include "exlimi.mm"

theorem zfcndreg
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let vv: setvar v
  let vu: setvar u
  let vt: setvar t

  disjoint x y
  disjoint x z
  disjoint y z
  disjoint w x
  disjoint v x
  disjoint u x
  disjoint t x
  disjoint w y
  disjoint v y
  disjoint u y
  disjoint t y
  disjoint w z
  disjoint v z
  disjoint u z
  disjoint t z
  disjoint v w
  disjoint u w
  disjoint t w
  disjoint u v
  disjoint t v
  disjoint t u
  assert |- ( E. y y e. x -> E. y ( y e. x /\ A. z ( z e. y -> -. z e. x ) ) )

  proof
    vy
    cv
    #
    vx
    cv
    #
    wcel
    #
    @2
    vz
    cv
    #
    @0
    wcel
    @3
    @1
    wcel
    wn
    wi
    vz
    wal
    wa
    #
    vy
    wex
    vy
    @4
    vy
    nfe1
    vy
    vx
    vz
    axregnd
    exlimi
end

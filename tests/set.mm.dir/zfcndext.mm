include "cv.mm"
include "wcel.mm"
include "wb.mm"
include "wceq.mm"
include "axextnd.mm"
include "19.36iv.mm"

theorem zfcndext
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
  assert |- ( A. z ( z e. x <-> z e. y ) -> x = y )

  proof
    vz
    cv
    #
    vx
    cv
    #
    wcel
    @0
    vy
    cv
    #
    wcel
    wb
    @1
    @2
    wceq
    vz
    vz
    vx
    vy
    axextnd
    19.36iv
end

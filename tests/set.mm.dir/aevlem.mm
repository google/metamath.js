include "weq.mm"
include "wal.mm"
include "cbvaev.mm"
include "aevlem0.mm"
include "4syl.mm"

theorem aevlem
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vt: setvar t
  let vu: setvar u

  disjoint x y
  disjoint t z
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint t u
  assert |- ( A. x x = y -> A. z z = t )

  proof
    vx
    vy
    weq
    vx
    wal
    vu
    vy
    weq
    vu
    wal
    vx
    vu
    weq
    vx
    wal
    vt
    vu
    weq
    vt
    wal
    vz
    vt
    weq
    vz
    wal
    vx
    vy
    vu
    cbvaev
    vu
    vy
    vx
    aevlem0
    vx
    vu
    vt
    cbvaev
    vt
    vu
    vz
    aevlem0
    4syl
end

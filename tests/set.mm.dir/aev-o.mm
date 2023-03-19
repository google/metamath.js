include "weq.mm"
include "wal.mm"
include "hbae-o.mm"
include "ax7.mm"
include "spimv.mm"
include "alrimih.mm"
include "equcomi.mm"
include "syl6.mm"
include "aecoms-o.mm"
include "axc4i-o.mm"
include "aecom-o.mm"
include "3syl.mm"

theorem aev-o
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let vv: setvar v
  let vt: setvar t
  let vu: setvar u

  disjoint x y
  disjoint t u
  disjoint t v
  disjoint u v
  disjoint t x
  disjoint t y
  disjoint u x
  disjoint u y
  disjoint u w
  assert |- ( A. x x = y -> A. z w = v )

  proof
    vx
    vy
    weq
    #
    vx
    wal
    #
    vw
    vv
    weq
    #
    vz
    vx
    vy
    vz
    hbae-o
    @1
    vt
    vy
    weq
    #
    vt
    wal
    #
    vu
    vv
    weq
    #
    vu
    wal
    #
    @2
    @1
    @3
    vt
    vx
    vy
    vt
    hbae-o
    @0
    @3
    vx
    vt
    vx
    vt
    vy
    ax7
    spimv
    alrimih
    @4
    vt
    vu
    weq
    #
    vt
    wal
    #
    vv
    vu
    weq
    #
    vv
    wal
    @6
    @3
    @7
    vt
    @7
    vy
    vt
    vy
    vt
    weq
    #
    @7
    vy
    vu
    vy
    vu
    weq
    @10
    vu
    vt
    weq
    @7
    vy
    vu
    vt
    ax7
    vu
    vt
    equcomi
    syl6
    spimv
    aecoms-o
    axc4i-o
    @8
    @9
    vv
    vt
    vu
    vv
    hbae-o
    @7
    @9
    vt
    vv
    vt
    vv
    vu
    ax7
    spimv
    alrimih
    vv
    vu
    aecom-o
    3syl
    @5
    @2
    vu
    vw
    vu
    vw
    vv
    ax7
    spimv
    3syl
    alrimih
end

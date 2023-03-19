include "weq.mm"
include "wal.mm"
include "wn.mm"
include "equidqe.mm"
include "ax10fromc7.mm"
include "hbequid.mm"
include "con3i.mm"
include "alrimih.mm"
include "mt3.mm"

theorem equidq
  let vx: setvar x
  let vy: setvar y


  assert |- A. y x = x

  proof
    vx
    vx
    weq
    #
    vy
    wal
    #
    @0
    wn
    #
    vy
    wal
    vx
    vy
    equidqe
    @1
    wn
    @2
    vy
    @0
    vy
    ax10fromc7
    @0
    @1
    vx
    vy
    hbequid
    con3i
    alrimih
    mt3
end

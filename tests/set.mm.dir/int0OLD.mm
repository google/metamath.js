include "cv.mm"
include "c0.mm"
include "wcel.mm"
include "wi.mm"
include "wal.mm"
include "cab.mm"
include "weq.mm"
include "cint.mm"
include "cvv.mm"
include "noel.mm"
include "pm2.21i.mm"
include "ax-gen.mm"
include "equid.mm"
include "2th.mm"
include "abbii.mm"
include "df-int.mm"
include "df-v.mm"
include "3eqtr4i.mm"

theorem int0OLD
  let vx: setvar x
  let vy: setvar y


  assert |- |^| (/) = _V

  proof
    vy
    cv
    #
    c0
    wcel
    #
    vx
    cv
    @0
    wcel
    #
    wi
    #
    vy
    wal
    #
    vx
    cab
    vx
    vx
    weq
    #
    vx
    cab
    c0
    cint
    cvv
    @4
    @5
    vx
    @4
    @5
    @3
    vy
    @1
    @2
    @0
    noel
    pm2.21i
    ax-gen
    vx
    equid
    2th
    abbii
    vx
    vy
    c0
    df-int
    vx
    df-v
    3eqtr4i
end

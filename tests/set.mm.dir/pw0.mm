include "cv.mm"
include "c0.mm"
include "wss.mm"
include "cab.mm"
include "wceq.mm"
include "cpw.mm"
include "csn.mm"
include "ss0b.mm"
include "abbii.mm"
include "df-pw.mm"
include "df-sn.mm"
include "3eqtr4i.mm"

theorem pw0
  let vx: setvar x


  assert |- ~P (/) = { (/) }

  proof
    vx
    cv
    #
    c0
    wss
    #
    vx
    cab
    @0
    c0
    wceq
    #
    vx
    cab
    c0
    cpw
    c0
    csn
    @1
    @2
    vx
    @0
    ss0b
    abbii
    vx
    c0
    df-pw
    vx
    c0
    df-sn
    3eqtr4i
end

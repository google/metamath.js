include "weq.mm"
include "wal.mm"
include "wn.mm"
include "wsb.mm"
include "wb.mm"
include "wnf.mm"
include "nfeqf.mm"
include "ex.mm"
include "sbft.mm"
include "syl6com.mm"
include "sbequ12r.mm"
include "equcoms.mm"
include "sps.mm"
include "pm2.61d2.mm"

theorem wl-equsb4
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( -. A. x x = z -> ( [ y / x ] y = z <-> y = z ) )

  proof
    vx
    vz
    weq
    vx
    wal
    wn
    #
    vx
    vy
    weq
    #
    vx
    wal
    #
    vy
    vz
    weq
    #
    vx
    vy
    wsb
    @3
    wb
    #
    @2
    wn
    #
    @0
    @3
    vx
    wnf
    #
    @4
    @5
    @0
    @6
    vy
    vz
    vx
    nfeqf
    ex
    @3
    vx
    vy
    sbft
    syl6com
    @1
    @4
    vx
    @4
    vy
    vx
    @3
    vy
    vx
    sbequ12r
    equcoms
    sps
    pm2.61d2
end

include "weq.mm"
include "wal.mm"
include "wn.mm"
include "wsb.mm"
include "nfv.mm"
include "nfna1.mm"
include "nfeqf2.mm"
include "wb.mm"
include "wi.mm"
include "equequ1.mm"
include "a1i.mm"
include "sbied.mm"
include "sbbid.mm"
include "sbcom3.mm"
include "sbf.mm"
include "bitri.mm"
include "equsb3.mm"
include "3bitr3g.mm"

theorem wl-equsb3
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w


  assert |- ( -. A. y y = z -> ( [ x / y ] y = z <-> x = z ) )

  proof
    vy
    vz
    weq
    #
    vy
    wal
    wn
    #
    @0
    vy
    vw
    wsb
    #
    vw
    vx
    wsb
    #
    vw
    vz
    weq
    #
    vw
    vx
    wsb
    @0
    vy
    vx
    wsb
    #
    vx
    vz
    weq
    @1
    @2
    @4
    vw
    vx
    @1
    vw
    nfv
    @1
    @0
    @4
    vy
    vw
    @0
    vy
    nfna1
    vy
    vz
    vw
    nfeqf2
    vy
    vw
    weq
    @0
    @4
    wb
    wi
    @1
    vy
    vw
    vz
    equequ1
    a1i
    sbied
    sbbid
    @3
    @5
    vw
    vx
    wsb
    @5
    @0
    vy
    vw
    vx
    sbcom3
    @5
    vw
    vx
    @5
    vw
    nfv
    sbf
    bitri
    vx
    vw
    vz
    equsb3
    3bitr3g
end

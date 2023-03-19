include "weq.mm"
include "wal.mm"
include "wn.mm"
include "wel.mm"
include "wi.mm"
include "hbn1.mm"
include "dveel2.mm"
include "hbim1.mm"
include "elequ1.mm"
include "imbi2d.mm"
include "dvelim.mm"
include "nfa1.mm"
include "nfn.mm"
include "19.21.mm"
include "syl6ib.mm"
include "pm2.86d.mm"

theorem axc14
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w


  assert |- ( -. A. z z = x -> ( -. A. z z = y -> ( x e. y -> A. z x e. y ) ) )

  proof
    vz
    vx
    weq
    vz
    wal
    wn
    #
    vz
    vy
    weq
    #
    vz
    wal
    #
    wn
    #
    vx
    vy
    wel
    #
    @4
    vz
    wal
    #
    @0
    @3
    @4
    wi
    #
    @6
    vz
    wal
    @3
    @5
    wi
    @3
    vw
    vy
    wel
    #
    wi
    @6
    vz
    vx
    vw
    @3
    @7
    vz
    @1
    vz
    hbn1
    vz
    vy
    vw
    dveel2
    hbim1
    vw
    vx
    weq
    @7
    @4
    @3
    vw
    vx
    vy
    elequ1
    imbi2d
    dvelim
    @3
    @4
    vz
    @2
    vz
    @1
    vz
    nfa1
    nfn
    19.21
    syl6ib
    pm2.86d
end

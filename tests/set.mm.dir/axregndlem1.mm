include "wel.mm"
include "wex.mm"
include "weq.mm"
include "wal.mm"
include "wn.mm"
include "wi.mm"
include "wa.mm"
include "19.8a.mm"
include "nfae.mm"
include "elirrv.mm"
include "elequ1.mm"
include "mtbii.mm"
include "sps.mm"
include "pm2.21d.mm"
include "alrimi.mm"
include "anim2i.mm"
include "expcom.mm"
include "eximd.mm"
include "syl5.mm"

theorem axregndlem1
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( A. x x = z -> ( x e. y -> E. x ( x e. y /\ A. z ( z e. x -> -. z e. y ) ) ) )

  proof
    vx
    vy
    wel
    #
    @0
    vx
    wex
    vx
    vz
    weq
    #
    vx
    wal
    #
    @0
    vz
    vx
    wel
    #
    vz
    vy
    wel
    wn
    #
    wi
    #
    vz
    wal
    #
    wa
    #
    vx
    wex
    @0
    vx
    19.8a
    @2
    @0
    @7
    vx
    vx
    vz
    vx
    nfae
    @0
    @2
    @7
    @2
    @6
    @0
    @2
    @5
    vz
    vx
    vz
    vz
    nfae
    @2
    @3
    @4
    @1
    @3
    wn
    vx
    @1
    vx
    vx
    wel
    @3
    vx
    elirrv
    vx
    vz
    vx
    elequ1
    mtbii
    sps
    pm2.21d
    alrimi
    anim2i
    expcom
    eximd
    syl5
end

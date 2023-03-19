include "csetrecs.mm"
include "cv.mm"
include "wss.mm"
include "cfv.mm"
include "wi.mm"
include "wal.mm"
include "cab.mm"
include "cuni.mm"
include "df-setrecs.mm"
include "nfv.mm"
include "nfcv.mm"
include "nffv.mm"
include "nfss.mm"
include "nfim.mm"
include "nfal.mm"
include "nfab.mm"
include "nfuni.mm"
include "nfcxfr.mm"

theorem nfsetrecs
  let vx: setvar x
  let cF: class F
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let vk: setvar k
  assume nfsetrecs.1: |- F/_ x F


  assert |- F/_ x setrecs ( F )

  proof
    vx
    cF
    csetrecs
    vw
    cv
    #
    vy
    cv
    #
    wss
    #
    @0
    vz
    cv
    #
    wss
    #
    @0
    cF
    cfv
    #
    @3
    wss
    #
    wi
    #
    wi
    #
    vw
    wal
    #
    @1
    @3
    wss
    #
    wi
    #
    vz
    wal
    #
    vy
    cab
    #
    cuni
    vy
    vz
    vw
    cF
    df-setrecs
    vx
    @13
    @12
    vx
    vy
    @11
    vx
    vz
    @9
    @10
    vx
    @8
    vx
    vw
    @2
    @7
    vx
    @2
    vx
    nfv
    @4
    @6
    vx
    @4
    vx
    nfv
    vx
    @5
    @3
    vx
    @0
    cF
    nfsetrecs.1
    vx
    @0
    nfcv
    nffv
    vx
    @3
    nfcv
    nfss
    nfim
    nfim
    nfal
    @10
    vx
    nfv
    nfim
    nfal
    nfab
    nfuni
    nfcxfr
end

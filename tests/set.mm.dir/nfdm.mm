include "cdm.mm"
include "cv.mm"
include "wbr.mm"
include "wex.mm"
include "cab.mm"
include "df-dm.mm"
include "nfcv.mm"
include "nfbr.mm"
include "nfex.mm"
include "nfab.mm"
include "nfcxfr.mm"

theorem nfdm
  let vx: setvar x
  let cA: class A
  let vy: setvar y
  let vz: setvar z
  assume nfrn.1: |- F/_ x A


  assert |- F/_ x dom A

  proof
    vx
    cA
    cdm
    vy
    cv
    #
    vz
    cv
    #
    cA
    wbr
    #
    vz
    wex
    #
    vy
    cab
    vy
    vz
    cA
    df-dm
    @3
    vx
    vy
    @2
    vx
    vz
    vx
    @0
    @1
    cA
    vx
    @0
    nfcv
    nfrn.1
    vx
    @1
    nfcv
    nfbr
    nfex
    nfab
    nfcxfr
end

include "cpw.mm"
include "cv.mm"
include "wss.mm"
include "cab.mm"
include "df-pw.mm"
include "nfcv.mm"
include "nfss.mm"
include "nfab.mm"
include "nfcxfr.mm"

theorem nfpw
  let vx: setvar x
  let cA: class A
  let vy: setvar y
  assume nfpw.1: |- F/_ x A


  assert |- F/_ x ~P A

  proof
    vx
    cA
    cpw
    vy
    cv
    #
    cA
    wss
    #
    vy
    cab
    vy
    cA
    df-pw
    @1
    vx
    vy
    vx
    @0
    cA
    vx
    @0
    nfcv
    nfpw.1
    nfss
    nfab
    nfcxfr
end

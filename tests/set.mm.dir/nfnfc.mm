include "wnfc.mm"
include "cv.mm"
include "wcel.mm"
include "wnf.mm"
include "wal.mm"
include "df-nfc.mm"
include "nfcr.mm"
include "ax-mp.mm"
include "nfnf.mm"
include "nfal.mm"
include "nfxfr.mm"

theorem nfnfc
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let vz: setvar z
  let cB: class B
  assume nfnfc.1: |- F/_ x A


  assert |- F/ x F/_ y A

  proof
    vy
    cA
    wnfc
    vz
    cv
    cA
    wcel
    #
    vy
    wnf
    #
    vz
    wal
    vx
    vy
    vz
    cA
    df-nfc
    @1
    vx
    vz
    @0
    vx
    vy
    vx
    cA
    wnfc
    @0
    vx
    wnf
    nfnfc.1
    vx
    vz
    cA
    nfcr
    ax-mp
    nfnf
    nfal
    nfxfr
end

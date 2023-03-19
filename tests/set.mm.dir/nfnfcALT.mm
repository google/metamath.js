include "wnfc.mm"
include "cv.mm"
include "wcel.mm"
include "wnf.mm"
include "wal.mm"
include "df-nfc.mm"
include "nfcri.mm"
include "nfnf.mm"
include "nfal.mm"
include "nfxfr.mm"

theorem nfnfcALT
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
    vz
    cA
    nfnfc.1
    nfcri
    nfnf
    nfal
    nfxfr
end

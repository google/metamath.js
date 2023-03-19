include "wnfc.mm"
include "cv.mm"
include "wcel.mm"
include "wnf.mm"
include "wal.mm"
include "df-nfc.mm"
include "nfnf1.mm"
include "nfal.mm"
include "nfxfr.mm"

theorem nfnfc1
  let vx: setvar x
  let cA: class A
  let vy: setvar y
  let wph: wff ph


  assert |- F/ x F/_ x A

  proof
    vx
    cA
    wnfc
    vy
    cv
    cA
    wcel
    #
    vx
    wnf
    #
    vy
    wal
    vx
    vx
    vy
    cA
    df-nfc
    @1
    vx
    vy
    @0
    vx
    nfnf1
    nfal
    nfxfr
end

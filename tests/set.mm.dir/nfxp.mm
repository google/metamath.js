include "cxp.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "copab.mm"
include "df-xp.mm"
include "nfcri.mm"
include "nfan.mm"
include "nfopab.mm"
include "nfcxfr.mm"

theorem nfxp
  let vx: setvar x
  let cA: class A
  let cB: class B
  let vy: setvar y
  let vz: setvar z
  assume nfxp.1: |- F/_ x A
  assume nfxp.2: |- F/_ x B


  assert |- F/_ x ( A X. B )

  proof
    vx
    cA
    cB
    cxp
    vy
    cv
    cA
    wcel
    #
    vz
    cv
    cB
    wcel
    #
    wa
    #
    vy
    vz
    copab
    vy
    vz
    cA
    cB
    df-xp
    @2
    vy
    vz
    vx
    @0
    @1
    vx
    vx
    vy
    cA
    nfxp.1
    nfcri
    vx
    vz
    cB
    nfxp.2
    nfcri
    nfan
    nfopab
    nfcxfr
end

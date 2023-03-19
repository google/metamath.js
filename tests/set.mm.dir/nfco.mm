include "ccom.mm"
include "cv.mm"
include "wbr.mm"
include "wa.mm"
include "wex.mm"
include "copab.mm"
include "df-co.mm"
include "nfcv.mm"
include "nfbr.mm"
include "nfan.mm"
include "nfex.mm"
include "nfopab.mm"
include "nfcxfr.mm"

theorem nfco
  let vx: setvar x
  let cA: class A
  let cB: class B
  let vw: setvar w
  let vy: setvar y
  let vz: setvar z
  assume nfco.1: |- F/_ x A
  assume nfco.2: |- F/_ x B


  assert |- F/_ x ( A o. B )

  proof
    vx
    cA
    cB
    ccom
    vy
    cv
    #
    vw
    cv
    #
    cB
    wbr
    #
    @1
    vz
    cv
    #
    cA
    wbr
    #
    wa
    #
    vw
    wex
    #
    vy
    vz
    copab
    vy
    vz
    vw
    cA
    cB
    df-co
    @6
    vy
    vz
    vx
    @5
    vx
    vw
    @2
    @4
    vx
    vx
    @0
    @1
    cB
    vx
    @0
    nfcv
    nfco.2
    vx
    @1
    nfcv
    #
    nfbr
    vx
    @1
    @3
    cA
    @7
    nfco.1
    vx
    @3
    nfcv
    nfbr
    nfan
    nfex
    nfopab
    nfcxfr
end

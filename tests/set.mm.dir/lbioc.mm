include "cioc.mm"
include "co.mm"
include "wcel.mm"
include "clt.mm"
include "wbr.mm"
include "cxr.mm"
include "w3a.mm"
include "cle.mm"
include "wa.mm"
include "df-ioc.mm"
include "elixx3g.mm"
include "biimpi.mm"
include "simprld.mm"
include "wn.mm"
include "cv.mm"
include "crab.mm"
include "elmpt2cl1.mm"
include "xrltnr.mm"
include "syl.mm"
include "pm2.65i.mm"

theorem lbioc
  let cA: class A
  let cB: class B
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- -. A e. ( A (,] B )

  proof
    cA
    cA
    cB
    cioc
    co
    wcel
    #
    cA
    cA
    clt
    wbr
    #
    @0
    cA
    cxr
    wcel
    #
    cB
    cxr
    wcel
    @2
    w3a
    #
    @1
    cA
    cB
    cle
    wbr
    #
    @0
    @3
    @1
    @4
    wa
    wa
    vx
    vy
    vz
    cA
    cB
    cA
    clt
    cle
    cioc
    vx
    vy
    vz
    df-ioc
    #
    elixx3g
    biimpi
    simprld
    @0
    @2
    @1
    wn
    vx
    vy
    cxr
    cxr
    vx
    cv
    vz
    cv
    #
    clt
    wbr
    @6
    vy
    cv
    cle
    wbr
    wa
    vz
    cxr
    crab
    cA
    cB
    cioc
    cA
    @5
    elmpt2cl1
    cA
    xrltnr
    syl
    pm2.65i
end

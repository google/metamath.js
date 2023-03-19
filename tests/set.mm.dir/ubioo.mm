include "cioo.mm"
include "co.mm"
include "wcel.mm"
include "clt.mm"
include "wbr.mm"
include "cxr.mm"
include "w3a.mm"
include "wa.mm"
include "elioo3g.mm"
include "simprbi.mm"
include "simprd.mm"
include "wn.mm"
include "simplbi.mm"
include "simp2d.mm"
include "xrltnr.mm"
include "syl.mm"
include "pm2.65i.mm"

theorem ubioo
  let cA: class A
  let cB: class B
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cC: class C
  let cD: class D


  assert |- -. B e. ( A (,) B )

  proof
    cB
    cA
    cB
    cioo
    co
    wcel
    #
    cB
    cB
    clt
    wbr
    #
    @0
    cA
    cB
    clt
    wbr
    #
    @1
    @0
    cA
    cxr
    wcel
    #
    cB
    cxr
    wcel
    #
    @4
    w3a
    #
    @2
    @1
    wa
    #
    cA
    cB
    cB
    elioo3g
    #
    simprbi
    simprd
    @0
    @4
    @1
    wn
    @0
    @3
    @4
    @4
    @0
    @5
    @6
    @7
    simplbi
    simp2d
    cB
    xrltnr
    syl
    pm2.65i
end

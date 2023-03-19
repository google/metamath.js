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
include "simpld.mm"
include "wn.mm"
include "simplbi.mm"
include "simp3d.mm"
include "xrltnr.mm"
include "syl.mm"
include "pm2.65i.mm"

theorem lbioo
  let cA: class A
  let cB: class B
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cC: class C
  let cD: class D


  assert |- -. A e. ( A (,) B )

  proof
    cA
    cA
    cB
    cioo
    co
    wcel
    #
    cA
    cA
    clt
    wbr
    #
    @0
    @1
    cA
    cB
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
    #
    @3
    w3a
    #
    @1
    @2
    wa
    #
    cA
    cB
    cA
    elioo3g
    #
    simprbi
    simpld
    @0
    @3
    @1
    wn
    @0
    @3
    @4
    @3
    @0
    @5
    @6
    @7
    simplbi
    simp3d
    cA
    xrltnr
    syl
    pm2.65i
end

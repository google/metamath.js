include "cen.mm"
include "wbr.mm"
include "wacn.mm"
include "wcel.mm"
include "cdom.mm"
include "wi.mm"
include "ensym.mm"
include "endom.mm"
include "acndom2.mm"
include "3syl.mm"
include "syl.mm"
include "impbid.mm"

theorem acnen2
  let cA: class A
  let cX: class X
  let cY: class Y
  let vf: setvar f
  let vg: setvar g
  let vh: setvar h
  let vk: setvar k
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cB: class B


  assert |- ( X ~~ Y -> ( X e. AC_ A <-> Y e. AC_ A ) )

  proof
    cX
    cY
    cen
    wbr
    #
    cX
    cA
    wacn
    #
    wcel
    #
    cY
    @1
    wcel
    #
    @0
    cY
    cX
    cen
    wbr
    cY
    cX
    cdom
    wbr
    @2
    @3
    wi
    cX
    cY
    ensym
    cY
    cX
    endom
    cA
    cY
    cX
    acndom2
    3syl
    @0
    cX
    cY
    cdom
    wbr
    @3
    @2
    wi
    cX
    cY
    endom
    cA
    cX
    cY
    acndom2
    syl
    impbid
end

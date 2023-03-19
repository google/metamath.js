include "cen.mm"
include "wbr.mm"
include "wacn.mm"
include "cv.mm"
include "wcel.mm"
include "cdom.mm"
include "wi.mm"
include "ensym.mm"
include "endom.mm"
include "acndom.mm"
include "3syl.mm"
include "syl.mm"
include "impbid.mm"
include "eqrdv.mm"

theorem acnen
  let cA: class A
  let cB: class B
  let vf: setvar f
  let vg: setvar g
  let vh: setvar h
  let vk: setvar k
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cX: class X
  let cY: class Y


  assert |- ( A ~~ B -> AC_ A = AC_ B )

  proof
    cA
    cB
    cen
    wbr
    #
    vx
    cA
    wacn
    #
    cB
    wacn
    #
    @0
    vx
    cv
    #
    @1
    wcel
    #
    @3
    @2
    wcel
    #
    @0
    cB
    cA
    cen
    wbr
    cB
    cA
    cdom
    wbr
    @4
    @5
    wi
    cA
    cB
    ensym
    cB
    cA
    endom
    cB
    cA
    @3
    acndom
    3syl
    @0
    cA
    cB
    cdom
    wbr
    @5
    @4
    wi
    cA
    cB
    endom
    cA
    cB
    @3
    acndom
    syl
    impbid
    eqrdv
end

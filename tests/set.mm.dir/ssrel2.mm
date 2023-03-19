include "cxp.mm"
include "wss.mm"
include "cv.mm"
include "cop.mm"
include "wcel.mm"
include "wi.mm"
include "wral.mm"
include "wa.mm"
include "ssel.mm"
include "a1d.mm"
include "ralrimivv.mm"
include "wceq.mm"
include "wrex.mm"
include "wal.mm"
include "eleq1.mm"
include "imbi12d.mm"
include "biimprcd.mm"
include "2ralimi.mm"
include "r19.23v.mm"
include "ralbii.mm"
include "bitri.mm"
include "sylib.mm"
include "com23.mm"
include "a2d.mm"
include "alimdv.mm"
include "dfss2.mm"
include "elxp2.mm"
include "imbi2i.mm"
include "albii.mm"
include "3imtr4g.mm"
include "com12.mm"
include "impbid2.mm"

theorem ssrel2
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cR: class R
  let cS: class S
  let vz: setvar z

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B x
  disjoint B y
  disjoint R x
  disjoint R y
  disjoint S x
  disjoint S y
  disjoint x z
  disjoint y z
  disjoint A z
  disjoint B z
  disjoint R z
  disjoint S z
  assert |- ( R C_ ( A X. B ) -> ( R C_ S <-> A. x e. A A. y e. B ( <. x , y >. e. R -> <. x , y >. e. S ) ) )

  proof
    cR
    cA
    cB
    cxp
    #
    wss
    #
    cR
    cS
    wss
    #
    vx
    cv
    #
    vy
    cv
    #
    cop
    #
    cR
    wcel
    #
    @5
    cS
    wcel
    #
    wi
    #
    vy
    cB
    wral
    vx
    cA
    wral
    #
    @2
    @8
    vx
    vy
    cA
    cB
    @2
    @8
    @3
    cA
    wcel
    @4
    cB
    wcel
    wa
    cR
    cS
    @5
    ssel
    a1d
    ralrimivv
    @9
    @1
    @2
    @9
    vz
    cv
    #
    cR
    wcel
    #
    @10
    @5
    wceq
    #
    vy
    cB
    wrex
    #
    vx
    cA
    wrex
    #
    wi
    #
    vz
    wal
    #
    @11
    @10
    cS
    wcel
    #
    wi
    #
    vz
    wal
    @1
    @2
    @9
    @15
    @18
    vz
    @9
    @11
    @14
    @17
    @9
    @14
    @11
    @17
    @9
    @12
    @18
    wi
    #
    vy
    cB
    wral
    #
    vx
    cA
    wral
    #
    @14
    @18
    wi
    #
    @8
    @19
    vx
    vy
    cA
    cB
    @12
    @18
    @8
    @12
    @11
    @6
    @17
    @7
    @10
    @5
    cR
    eleq1
    @10
    @5
    cS
    eleq1
    imbi12d
    biimprcd
    2ralimi
    @21
    @13
    @18
    wi
    #
    vx
    cA
    wral
    @22
    @20
    @23
    vx
    cA
    @12
    @18
    vy
    cB
    r19.23v
    ralbii
    @13
    @18
    vx
    cA
    r19.23v
    bitri
    sylib
    com23
    a2d
    alimdv
    @1
    @11
    @10
    @0
    wcel
    #
    wi
    #
    vz
    wal
    @16
    vz
    cR
    @0
    dfss2
    @25
    @15
    vz
    @24
    @14
    @11
    vx
    vy
    @10
    cA
    cB
    elxp2
    imbi2i
    albii
    bitri
    vz
    cR
    cS
    dfss2
    3imtr4g
    com12
    impbid2
end

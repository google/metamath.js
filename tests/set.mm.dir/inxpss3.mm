include "cv.mm"
include "cxp.mm"
include "cin.mm"
include "wbr.mm"
include "wi.mm"
include "wal.mm"
include "wcel.mm"
include "wa.mm"
include "wral.mm"
include "brinxp2ALTV.mm"
include "imbi12i.mm"
include "imdistan.mm"
include "bitr4i.mm"
include "2albii.mm"
include "r2al.mm"

theorem inxpss3
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cR: class R
  let cS: class S

  disjoint x y
  disjoint A y
  assert |- ( A. x A. y ( x ( R i^i ( A X. B ) ) y -> x ( S i^i ( A X. B ) ) y ) <-> A. x e. A A. y e. B ( x R y -> x S y ) )

  proof
    vx
    cv
    #
    vy
    cv
    #
    cR
    cA
    cB
    cxp
    #
    cin
    wbr
    #
    @0
    @1
    cS
    @2
    cin
    wbr
    #
    wi
    #
    vy
    wal
    vx
    wal
    @0
    cA
    wcel
    @1
    cB
    wcel
    wa
    #
    @0
    @1
    cR
    wbr
    #
    @0
    @1
    cS
    wbr
    #
    wi
    #
    wi
    #
    vy
    wal
    vx
    wal
    @9
    vy
    cB
    wral
    vx
    cA
    wral
    @5
    @10
    vx
    vy
    @5
    @6
    @7
    wa
    #
    @6
    @8
    wa
    #
    wi
    @10
    @3
    @11
    @4
    @12
    cA
    cB
    @0
    @1
    cR
    brinxp2ALTV
    cA
    cB
    @0
    @1
    cS
    brinxp2ALTV
    imbi12i
    @6
    @7
    @8
    imdistan
    bitr4i
    2albii
    @9
    vx
    vy
    cA
    cB
    r2al
    bitr4i
end

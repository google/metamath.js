include "cv.mm"
include "cxp.mm"
include "cin.mm"
include "wbr.mm"
include "wi.mm"
include "wal.mm"
include "wcel.mm"
include "wa.mm"
include "wss.mm"
include "wral.mm"
include "brinxp2ALTV.mm"
include "imbi1i.mm"
include "impexp.mm"
include "bitri.mm"
include "2albii.mm"
include "wrel.mm"
include "wb.mm"
include "relinxp.mm"
include "ssrel3.mm"
include "ax-mp.mm"
include "r2al.mm"
include "3bitr4i.mm"

theorem inxpss
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cR: class R
  let cS: class S

  disjoint A x
  disjoint A y
  disjoint x y
  disjoint B x
  disjoint B y
  disjoint R x
  disjoint R y
  disjoint S x
  disjoint S y
  assert |- ( ( R i^i ( A X. B ) ) C_ S <-> A. x e. A A. y e. B ( x R y -> x S y ) )

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
    cin
    #
    wbr
    #
    @0
    @1
    cS
    wbr
    #
    wi
    #
    vy
    wal
    vx
    wal
    #
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
    @4
    wi
    #
    wi
    #
    vy
    wal
    vx
    wal
    @2
    cS
    wss
    #
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
    @7
    @8
    wa
    #
    @4
    wi
    @10
    @3
    @12
    @4
    cA
    cB
    @0
    @1
    cR
    brinxp2ALTV
    imbi1i
    @7
    @8
    @4
    impexp
    bitri
    2albii
    @2
    wrel
    @11
    @6
    wb
    cA
    cB
    cR
    relinxp
    vx
    vy
    @2
    cS
    ssrel3
    ax-mp
    @9
    vx
    vy
    cA
    cB
    r2al
    3bitr4i
end

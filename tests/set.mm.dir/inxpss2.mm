include "cxp.mm"
include "cin.mm"
include "wss.mm"
include "cv.mm"
include "wbr.mm"
include "wi.mm"
include "wal.mm"
include "wral.mm"
include "wrel.mm"
include "wb.mm"
include "relinxp.mm"
include "ssrel3.mm"
include "ax-mp.mm"
include "inxpss3.mm"
include "bitri.mm"

theorem inxpss2
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
  assert |- ( ( R i^i ( A X. B ) ) C_ ( S i^i ( A X. B ) ) <-> A. x e. A A. y e. B ( x R y -> x S y ) )

  proof
    cR
    cA
    cB
    cxp
    #
    cin
    #
    cS
    @0
    cin
    #
    wss
    #
    vx
    cv
    #
    vy
    cv
    #
    @1
    wbr
    @4
    @5
    @2
    wbr
    wi
    vy
    wal
    vx
    wal
    #
    @4
    @5
    cR
    wbr
    @4
    @5
    cS
    wbr
    wi
    vy
    cB
    wral
    vx
    cA
    wral
    @1
    wrel
    @3
    @6
    wb
    cA
    cB
    cR
    relinxp
    vx
    vy
    @1
    @2
    ssrel3
    ax-mp
    vx
    vy
    cA
    cB
    cR
    cS
    inxpss3
    bitri
end

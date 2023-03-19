include "cid.mm"
include "cxp.mm"
include "cin.mm"
include "wss.mm"
include "cv.mm"
include "wbr.mm"
include "wi.mm"
include "wral.mm"
include "wceq.mm"
include "inxpss.mm"
include "wb.mm"
include "cvv.mm"
include "ideqg.mm"
include "elv.mm"
include "imbi1i.mm"
include "2ralbii.mm"
include "bitri.mm"

theorem idinxpss
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cR: class R

  disjoint A x
  disjoint A y
  disjoint x y
  disjoint B x
  disjoint B y
  disjoint R x
  disjoint R y
  assert |- ( ( _I i^i ( A X. B ) ) C_ R <-> A. x e. A A. y e. B ( x = y -> x R y ) )

  proof
    cid
    cA
    cB
    cxp
    cin
    cR
    wss
    vx
    cv
    #
    vy
    cv
    #
    cid
    wbr
    #
    @0
    @1
    cR
    wbr
    #
    wi
    #
    vy
    cB
    wral
    vx
    cA
    wral
    @0
    @1
    wceq
    #
    @3
    wi
    #
    vy
    cB
    wral
    vx
    cA
    wral
    vx
    vy
    cA
    cB
    cid
    cR
    inxpss
    @4
    @6
    vx
    vy
    cA
    cB
    @2
    @5
    @3
    @2
    @5
    wb
    vy
    @0
    @1
    cvv
    ideqg
    elv
    imbi1i
    2ralbii
    bitri
end

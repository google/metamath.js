include "cxp.mm"
include "cin.mm"
include "cid.mm"
include "wss.mm"
include "cv.mm"
include "wbr.mm"
include "wi.mm"
include "wral.mm"
include "wceq.mm"
include "inxpss2.mm"
include "wb.mm"
include "cvv.mm"
include "ideqg.mm"
include "elv.mm"
include "imbi2i.mm"
include "2ralbii.mm"
include "bitri.mm"

theorem inxpssidinxp
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
  assert |- ( ( R i^i ( A X. B ) ) C_ ( _I i^i ( A X. B ) ) <-> A. x e. A A. y e. B ( x R y -> x = y ) )

  proof
    cR
    cA
    cB
    cxp
    #
    cin
    cid
    @0
    cin
    wss
    vx
    cv
    #
    vy
    cv
    #
    cR
    wbr
    #
    @1
    @2
    cid
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
    @3
    @1
    @2
    wceq
    #
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
    cR
    cid
    inxpss2
    @5
    @7
    vx
    vy
    cA
    cB
    @4
    @6
    @3
    @4
    @6
    wb
    vy
    @1
    @2
    cvv
    ideqg
    elv
    imbi2i
    2ralbii
    bitri
end

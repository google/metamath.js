include "cid.mm"
include "cxp.mm"
include "cin.mm"
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
include "imbi1i.mm"
include "2ralbii.mm"
include "bitri.mm"

theorem idinxpssinxp
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
  assert |- ( ( _I i^i ( A X. B ) ) C_ ( R i^i ( A X. B ) ) <-> A. x e. A A. y e. B ( x = y -> x R y ) )

  proof
    cid
    cA
    cB
    cxp
    #
    cin
    cR
    @0
    cin
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
    @1
    @2
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
    @1
    @2
    wceq
    #
    @4
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
    inxpss2
    @5
    @7
    vx
    vy
    cA
    cB
    @3
    @6
    @4
    @3
    @6
    wb
    vy
    @1
    @2
    cvv
    ideqg
    elv
    imbi1i
    2ralbii
    bitri
end

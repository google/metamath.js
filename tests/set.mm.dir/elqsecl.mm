include "wcel.mm"
include "cqs.mm"
include "cv.mm"
include "cec.mm"
include "wceq.mm"
include "wrex.mm"
include "wbr.mm"
include "cab.mm"
include "elqsg.mm"
include "cvv.mm"
include "vex.mm"
include "dfec2.mm"
include "mp1i.mm"
include "eqeq2d.mm"
include "rexbidv.mm"
include "bitrd.mm"

theorem elqsecl
  let vx: setvar x
  let vy: setvar y
  let cB: class B
  let c.sm: class .~
  let cW: class W
  let cX: class X

  disjoint .~ x
  disjoint .~ y
  disjoint x y
  disjoint B x
  disjoint W x
  disjoint X x
  assert |- ( B e. X -> ( B e. ( W /. .~ ) <-> E. x e. W B = { y | x .~ y } ) )

  proof
    cB
    cX
    wcel
    #
    cB
    cW
    c.sm
    cqs
    wcel
    cB
    vx
    cv
    #
    c.sm
    cec
    #
    wceq
    #
    vx
    cW
    wrex
    cB
    @1
    vy
    cv
    c.sm
    wbr
    vy
    cab
    #
    wceq
    #
    vx
    cW
    wrex
    vx
    cW
    cB
    c.sm
    cX
    elqsg
    @0
    @3
    @5
    vx
    cW
    @0
    @2
    @4
    cB
    @1
    cvv
    wcel
    @2
    @4
    wceq
    @0
    vx
    vex
    vy
    @1
    c.sm
    cvv
    dfec2
    mp1i
    eqeq2d
    rexbidv
    bitrd
end

include "cfn.mm"
include "wcel.mm"
include "cv.mm"
include "cen.mm"
include "wbr.mm"
include "com.mm"
include "wrex.mm"
include "cab.mm"
include "df-fin.mm"
include "eleq2i.mm"
include "cvv.mm"
include "relen.mm"
include "brrelexi.mm"
include "rexlimivw.mm"
include "wceq.mm"
include "breq1.mm"
include "rexbidv.mm"
include "elab3.mm"
include "bitri.mm"

theorem isfi
  let vx: setvar x
  let cA: class A
  let vy: setvar y
  let vf: setvar f

  disjoint A x
  disjoint x y
  disjoint f x
  disjoint f y
  disjoint A y
  disjoint A f
  assert |- ( A e. Fin <-> E. x e. _om A ~~ x )

  proof
    cA
    cfn
    wcel
    cA
    vy
    cv
    #
    vx
    cv
    #
    cen
    wbr
    #
    vx
    com
    wrex
    #
    vy
    cab
    #
    wcel
    cA
    @1
    cen
    wbr
    #
    vx
    com
    wrex
    #
    cfn
    @4
    cA
    vy
    vx
    df-fin
    eleq2i
    @3
    @6
    vy
    cA
    @5
    cA
    cvv
    wcel
    vx
    com
    cA
    @1
    cen
    relen
    brrelexi
    rexlimivw
    @0
    cA
    wceq
    @2
    @5
    vx
    com
    @0
    cA
    @1
    cen
    breq1
    rexbidv
    elab3
    bitri
end

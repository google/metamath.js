include "ccrd.mm"
include "cdm.mm"
include "wcel.mm"
include "cv.mm"
include "cen.mm"
include "wbr.mm"
include "con0.mm"
include "wrex.mm"
include "cab.mm"
include "cardf2.mm"
include "fdmi.mm"
include "eleq2i.mm"
include "cvv.mm"
include "relen.mm"
include "brrelex2i.mm"
include "rexlimivw.mm"
include "wceq.mm"
include "breq2.mm"
include "rexbidv.mm"
include "elab3.mm"
include "bitri.mm"

theorem isnum2
  let vx: setvar x
  let cA: class A
  let vw: setvar w
  let vy: setvar y
  let vz: setvar z
  let cB: class B

  disjoint A x
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint A w
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint B x
  assert |- ( A e. dom card <-> E. x e. On x ~~ A )

  proof
    cA
    ccrd
    cdm
    #
    wcel
    cA
    vx
    cv
    #
    vy
    cv
    #
    cen
    wbr
    #
    vx
    con0
    wrex
    #
    vy
    cab
    #
    wcel
    @1
    cA
    cen
    wbr
    #
    vx
    con0
    wrex
    #
    @0
    @5
    cA
    @5
    con0
    ccrd
    vy
    vx
    cardf2
    fdmi
    eleq2i
    @4
    @7
    vy
    cA
    @6
    cA
    cvv
    wcel
    vx
    con0
    @1
    cA
    cen
    relen
    brrelex2i
    rexlimivw
    @2
    cA
    wceq
    @3
    @6
    vx
    con0
    @2
    cA
    @1
    cen
    breq2
    rexbidv
    elab3
    bitri
end

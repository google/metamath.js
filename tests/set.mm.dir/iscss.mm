include "wcel.mm"
include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "cab.mm"
include "cssval.mm"
include "eleq2d.mm"
include "cvv.mm"
include "id.mm"
include "fvex.mm"
include "syl6eqel.mm"
include "fveq2.mm"
include "fveq2d.mm"
include "eqeq12d.mm"
include "elab3.mm"
include "syl6bb.mm"

theorem iscss
  let cC: class C
  let cS: class S
  let c.pe: class ._|_
  let cW: class W
  let cX: class X
  let vs: setvar s
  let vw: setvar w
  assume cssval.o: |- ._|_ = ( ocv ` W )
  assume cssval.c: |- C = ( CSubSp ` W )


  assert |- ( W e. X -> ( S e. C <-> S = ( ._|_ ` ( ._|_ ` S ) ) ) )

  proof
    cW
    cX
    wcel
    #
    cS
    cC
    wcel
    cS
    vs
    cv
    #
    @1
    c.pe
    cfv
    #
    c.pe
    cfv
    #
    wceq
    #
    vs
    cab
    #
    wcel
    cS
    cS
    c.pe
    cfv
    #
    c.pe
    cfv
    #
    wceq
    #
    @0
    cC
    @5
    cS
    cC
    c.pe
    cW
    cX
    vs
    cssval.o
    cssval.c
    cssval
    eleq2d
    @4
    @8
    vs
    cS
    @8
    cS
    @7
    cvv
    @8
    id
    @6
    c.pe
    fvex
    syl6eqel
    @1
    cS
    wceq
    #
    @1
    cS
    @3
    @7
    @9
    id
    @9
    @2
    @6
    c.pe
    @1
    cS
    c.pe
    fveq2
    fveq2d
    eqeq12d
    elab3
    syl6bb
end

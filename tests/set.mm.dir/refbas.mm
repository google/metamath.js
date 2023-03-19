include "cvv.mm"
include "wcel.mm"
include "cref.mm"
include "wbr.mm"
include "wceq.mm"
include "refrel.mm"
include "brrelexi.mm"
include "cv.mm"
include "wss.mm"
include "wrex.mm"
include "wral.mm"
include "isref.mm"
include "simprbda.mm"
include "mpancom.mm"

theorem refbas
  let cA: class A
  let cB: class B
  let cX: class X
  let cY: class Y
  let vx: setvar x
  let vy: setvar y
  assume refbas.1: |- X = U. A
  assume refbas.2: |- Y = U. B


  assert |- ( A Ref B -> Y = X )

  proof
    cA
    cvv
    wcel
    #
    cA
    cB
    cref
    wbr
    #
    cY
    cX
    wceq
    #
    cA
    cB
    cref
    refrel
    brrelexi
    @0
    @1
    @2
    vx
    cv
    vy
    cv
    wss
    vy
    cB
    wrex
    vx
    cA
    wral
    vx
    vy
    cA
    cB
    cvv
    cX
    cY
    refbas.1
    refbas.2
    isref
    simprbda
    mpancom
end

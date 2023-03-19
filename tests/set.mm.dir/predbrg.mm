include "wcel.mm"
include "cpred.mm"
include "wbr.mm"
include "cv.mm"
include "wi.mm"
include "wceq.mm"
include "predeq3.mm"
include "eleq2d.mm"
include "breq2.mm"
include "imbi12d.mm"
include "vex.mm"
include "elpredim.mm"
include "vtoclg.mm"
include "imp.mm"

theorem predbrg
  let cA: class A
  let cR: class R
  let cV: class V
  let cX: class X
  let cY: class Y
  let vx: setvar x


  assert |- ( ( X e. V /\ Y e. Pred ( R , A , X ) ) -> Y R X )

  proof
    cX
    cV
    wcel
    cY
    cA
    cR
    cX
    cpred
    #
    wcel
    #
    cY
    cX
    cR
    wbr
    #
    cY
    cA
    cR
    vx
    cv
    #
    cpred
    #
    wcel
    #
    cY
    @3
    cR
    wbr
    #
    wi
    @1
    @2
    wi
    vx
    cX
    cV
    @3
    cX
    wceq
    #
    @5
    @1
    @6
    @2
    @7
    @4
    @0
    cY
    cA
    cR
    @3
    cX
    predeq3
    eleq2d
    @3
    cX
    cY
    cR
    breq2
    imbi12d
    cA
    cR
    @3
    cY
    vx
    vex
    elpredim
    vtoclg
    imp
end

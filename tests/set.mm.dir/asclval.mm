include "cv.mm"
include "co.mm"
include "oveq1.mm"
include "asclfval.mm"
include "ovex.mm"
include "fvmpt.mm"

theorem asclval
  let cA: class A
  let c.x: class .x.
  let c.1: class .1.
  let cF: class F
  let cK: class K
  let cW: class W
  let cX: class X
  let vw: setvar w
  let vx: setvar x
  assume asclfval.a: |- A = ( algSc ` W )
  assume asclfval.f: |- F = ( Scalar ` W )
  assume asclfval.k: |- K = ( Base ` F )
  assume asclfval.s: |- .x. = ( .s ` W )
  assume asclfval.o: |- .1. = ( 1r ` W )


  assert |- ( X e. K -> ( A ` X ) = ( X .x. .1. ) )

  proof
    vx
    cX
    vx
    cv
    #
    c.1
    c.x
    co
    cX
    c.1
    c.x
    co
    cK
    cA
    @0
    cX
    c.1
    c.x
    oveq1
    vx
    cA
    c.x
    c.1
    cF
    cK
    cW
    asclfval.a
    asclfval.f
    asclfval.k
    asclfval.s
    asclfval.o
    asclfval
    cX
    c.1
    c.x
    ovex
    fvmpt
end

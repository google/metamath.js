include "wcel.mm"
include "cvv.mm"
include "char.mm"
include "cfv.mm"
include "cv.mm"
include "cdom.mm"
include "wbr.mm"
include "con0.mm"
include "crab.mm"
include "wceq.mm"
include "elex.mm"
include "breq2.mm"
include "rabbidv.mm"
include "df-har.mm"
include "hartogs.mm"
include "fvmpt3.mm"
include "syl.mm"

theorem harval
  let vy: setvar y
  let cV: class V
  let cX: class X
  let vx: setvar x
  let cY: class Y

  disjoint X y
  disjoint x y
  disjoint X x
  disjoint Y x
  disjoint Y y
  assert |- ( X e. V -> ( har ` X ) = { y e. On | y ~<_ X } )

  proof
    cX
    cV
    wcel
    cX
    cvv
    wcel
    cX
    char
    cfv
    vy
    cv
    #
    cX
    cdom
    wbr
    #
    vy
    con0
    crab
    #
    wceq
    cX
    cV
    elex
    vx
    cX
    @0
    vx
    cv
    #
    cdom
    wbr
    #
    vy
    con0
    crab
    @2
    cvv
    char
    con0
    @3
    cX
    wceq
    @4
    @1
    vy
    con0
    @3
    cX
    @0
    cdom
    breq2
    rabbidv
    vx
    vy
    df-har
    vy
    @3
    cvv
    hartogs
    fvmpt3
    syl
end

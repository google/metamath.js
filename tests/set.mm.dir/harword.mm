include "cdom.mm"
include "wbr.mm"
include "cv.mm"
include "con0.mm"
include "crab.mm"
include "char.mm"
include "cfv.mm"
include "wi.mm"
include "wcel.mm"
include "domtr.mm"
include "expcom.mm"
include "adantr.mm"
include "ss2rabdv.mm"
include "cvv.mm"
include "wceq.mm"
include "reldom.mm"
include "brrelexi.mm"
include "harval.mm"
include "syl.mm"
include "brrelex2i.mm"
include "3sstr4d.mm"

theorem harword
  let cX: class X
  let cY: class Y
  let vx: setvar x
  let vy: setvar y


  assert |- ( X ~<_ Y -> ( har ` X ) C_ ( har ` Y ) )

  proof
    cX
    cY
    cdom
    wbr
    #
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
    @1
    cY
    cdom
    wbr
    #
    vy
    con0
    crab
    #
    cX
    char
    cfv
    #
    cY
    char
    cfv
    #
    @0
    @2
    @4
    vy
    con0
    @0
    @2
    @4
    wi
    @1
    con0
    wcel
    @2
    @0
    @4
    @1
    cX
    cY
    domtr
    expcom
    adantr
    ss2rabdv
    @0
    cX
    cvv
    wcel
    @6
    @3
    wceq
    cX
    cY
    cdom
    reldom
    brrelexi
    vy
    cvv
    cX
    harval
    syl
    @0
    cY
    cvv
    wcel
    @7
    @5
    wceq
    cX
    cY
    cdom
    reldom
    brrelex2i
    vy
    cvv
    cY
    harval
    syl
    3sstr4d
end

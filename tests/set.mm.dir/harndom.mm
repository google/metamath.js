include "char.mm"
include "cfv.mm"
include "wcel.mm"
include "cdom.mm"
include "wbr.mm"
include "harcl.mm"
include "onirri.mm"
include "con0.mm"
include "elharval.mm"
include "mpbiran.mm"
include "mtbi.mm"

theorem harndom
  let cX: class X
  let vx: setvar x
  let vy: setvar y
  let cY: class Y


  assert |- -. ( har ` X ) ~<_ X

  proof
    cX
    char
    cfv
    #
    @0
    wcel
    #
    @0
    cX
    cdom
    wbr
    #
    @0
    cX
    harcl
    #
    onirri
    @1
    @0
    con0
    wcel
    @2
    @3
    cX
    @0
    elharval
    mpbiran
    mtbi
end

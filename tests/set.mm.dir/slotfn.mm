include "cvv.mm"
include "cv.mm"
include "cfv.mm"
include "fvex.mm"
include "cslot.mm"
include "cmpt.mm"
include "df-slot.mm"
include "eqtri.mm"
include "fnmpti.mm"

theorem slotfn
  let cE: class E
  let cN: class N
  let vx: setvar x
  let cS: class S
  assume strfvnd.c: |- E = Slot N


  assert |- E Fn _V

  proof
    vx
    cvv
    cN
    vx
    cv
    #
    cfv
    #
    cE
    cN
    @0
    fvex
    cE
    cN
    cslot
    vx
    cvv
    @1
    cmpt
    strfvnd.c
    vx
    cN
    df-slot
    eqtri
    fnmpti
end

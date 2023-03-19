include "cslot.mm"
include "cnx.mm"
include "cfv.mm"
include "cvv.mm"
include "cv.mm"
include "cmpt.mm"
include "df-slot.mm"
include "ndxarg.mm"
include "fveq2i.mm"
include "mpteq2i.mm"
include "eqtr4i.mm"

theorem ndxidOLD
  let cE: class E
  let cN: class N
  let vx: setvar x
  assume ndxarg.1: |- E = Slot N
  assume ndxarg.2: |- N e. NN


  assert |- E = Slot ( E ` ndx )

  proof
    cE
    cN
    cslot
    #
    cnx
    cE
    cfv
    #
    cslot
    #
    ndxarg.1
    @2
    vx
    cvv
    @1
    vx
    cv
    #
    cfv
    #
    cmpt
    #
    @0
    vx
    @1
    df-slot
    @0
    vx
    cvv
    cN
    @3
    cfv
    #
    cmpt
    @5
    vx
    cN
    df-slot
    vx
    cvv
    @4
    @6
    @1
    cN
    @3
    cE
    cN
    ndxarg.1
    ndxarg.2
    ndxarg
    fveq2i
    mpteq2i
    eqtr4i
    eqtr4i
    eqtr4i
end

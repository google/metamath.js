include "c1.mm"
include "cc0.mm"
include "cdc.mm"
include "cslot.mm"
include "cvv.mm"
include "c10.mm"
include "cv.mm"
include "cfv.mm"
include "cmpt.mm"
include "cple.mm"
include "df-slot.mm"
include "dec10OLD.mm"
include "eqcomi.mm"
include "fveq2i.mm"
include "mpteq2i.mm"
include "eqtri.mm"
include "df-ple.mm"
include "3eqtr4i.mm"

theorem dfpleOLD
  let vx: setvar x


  assert |- le = Slot 10

  proof
    c1
    cc0
    cdc
    #
    cslot
    #
    vx
    cvv
    c10
    vx
    cv
    #
    cfv
    #
    cmpt
    #
    cple
    c10
    cslot
    @1
    vx
    cvv
    @0
    @2
    cfv
    #
    cmpt
    @4
    vx
    @0
    df-slot
    vx
    cvv
    @5
    @3
    @0
    c10
    @2
    c10
    @0
    dec10OLD
    eqcomi
    fveq2i
    mpteq2i
    eqtri
    df-ple
    vx
    c10
    df-slot
    3eqtr4i
end

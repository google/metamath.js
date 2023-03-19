include "cnx.mm"
include "cfv.mm"
include "wceq.mm"
include "cslot.mm"
include "ndxarg.mm"
include "eqcomi.mm"
include "sloteq.mm"
include "syl5eq.mm"
include "ax-mp.mm"

theorem ndxid
  let cE: class E
  let cN: class N
  let vx: setvar x
  assume ndxarg.1: |- E = Slot N
  assume ndxarg.2: |- N e. NN


  assert |- E = Slot ( E ` ndx )

  proof
    cN
    cnx
    cE
    cfv
    #
    wceq
    #
    cE
    @0
    cslot
    #
    wceq
    @0
    cN
    cE
    cN
    ndxarg.1
    ndxarg.2
    ndxarg
    eqcomi
    @1
    cE
    cN
    cslot
    @2
    ndxarg.1
    cN
    @0
    sloteq
    syl5eq
    ax-mp
end

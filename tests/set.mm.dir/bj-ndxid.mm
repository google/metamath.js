include "cnx.mm"
include "cfv.mm"
include "wceq.mm"
include "cslot.mm"
include "bj-ndxarg.mm"
include "eqcomi.mm"
include "bj-evaleq.mm"
include "syl5eq.mm"
include "ax-mp.mm"

theorem bj-ndxid
  let cE: class E
  let cN: class N
  assume bj-ndxarg.1: |- E = Slot N
  assume bj-ndxarg.2: |- N e. NN


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
    bj-ndxarg.1
    bj-ndxarg.2
    bj-ndxarg
    eqcomi
    @1
    cE
    cN
    cslot
    @2
    bj-ndxarg.1
    cN
    @0
    bj-evaleq
    syl5eq
    ax-mp
end

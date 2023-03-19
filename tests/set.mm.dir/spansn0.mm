include "c0h.mm"
include "cspn.mm"
include "cfv.mm"
include "c0v.mm"
include "csn.mm"
include "df-ch0.mm"
include "fveq2i.mm"
include "csh.mm"
include "wcel.mm"
include "wceq.mm"
include "h0elsh.mm"
include "spanid.mm"
include "ax-mp.mm"
include "eqtr3i.mm"

theorem spansn0



  assert |- ( span ` { 0h } ) = 0H

  proof
    c0h
    cspn
    cfv
    #
    c0v
    csn
    #
    cspn
    cfv
    c0h
    c0h
    @1
    cspn
    df-ch0
    fveq2i
    c0h
    csh
    wcel
    @0
    c0h
    wceq
    h0elsh
    c0h
    spanid
    ax-mp
    eqtr3i
end

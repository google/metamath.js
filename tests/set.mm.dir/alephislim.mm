include "con0.mm"
include "wcel.mm"
include "com.mm"
include "cale.mm"
include "cfv.mm"
include "wss.mm"
include "wlim.mm"
include "alephgeom.mm"
include "ccrd.mm"
include "cardlim.mm"
include "alephcard.mm"
include "sseq2i.mm"
include "wceq.mm"
include "wb.mm"
include "limeq.mm"
include "ax-mp.mm"
include "3bitr3i.mm"
include "bitri.mm"

theorem alephislim
  let cA: class A


  assert |- ( A e. On <-> Lim ( aleph ` A ) )

  proof
    cA
    con0
    wcel
    com
    cA
    cale
    cfv
    #
    wss
    #
    @0
    wlim
    #
    cA
    alephgeom
    com
    @0
    ccrd
    cfv
    #
    wss
    @3
    wlim
    #
    @1
    @2
    @0
    cardlim
    @3
    @0
    com
    cA
    alephcard
    #
    sseq2i
    @3
    @0
    wceq
    @4
    @2
    wb
    @5
    @3
    @0
    limeq
    ax-mp
    3bitr3i
    bitri
end

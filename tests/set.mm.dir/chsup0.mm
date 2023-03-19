include "c0.mm"
include "chsup.mm"
include "cfv.mm"
include "c0h.mm"
include "wss.mm"
include "wceq.mm"
include "csn.mm"
include "0ss.mm"
include "cch.mm"
include "wi.mm"
include "wcel.mm"
include "h0elch.mm"
include "snssi.mm"
include "ax-mp.mm"
include "chsupss.mm"
include "mp2an.mm"
include "chsupsn.mm"
include "sseqtri.mm"
include "chsupcl.mm"
include "chle0i.mm"
include "mpbi.mm"

theorem chsup0



  assert |- ( \/H ` (/) ) = 0H

  proof
    c0
    chsup
    cfv
    #
    c0h
    wss
    @0
    c0h
    wceq
    @0
    c0h
    csn
    #
    chsup
    cfv
    #
    c0h
    c0
    @1
    wss
    #
    @0
    @2
    wss
    #
    @1
    0ss
    c0
    cch
    wss
    #
    @1
    cch
    wss
    #
    @3
    @4
    wi
    cch
    0ss
    #
    c0h
    cch
    wcel
    #
    @6
    h0elch
    c0h
    cch
    snssi
    ax-mp
    c0
    @1
    chsupss
    mp2an
    ax-mp
    @8
    @2
    c0h
    wceq
    h0elch
    c0h
    chsupsn
    ax-mp
    sseqtri
    @0
    @5
    @0
    cch
    wcel
    @7
    c0
    chsupcl
    ax-mp
    chle0i
    mpbi
end

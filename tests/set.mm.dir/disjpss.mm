include "cin.mm"
include "c0.mm"
include "wceq.mm"
include "wne.mm"
include "wa.mm"
include "wss.mm"
include "wn.mm"
include "cun.mm"
include "wpss.mm"
include "ssid.mm"
include "biantru.mm"
include "ssin.mm"
include "bitri.mm"
include "sseq2.mm"
include "syl5bb.mm"
include "ss0.mm"
include "syl6bi.mm"
include "necon3ad.mm"
include "imp.mm"
include "nsspssun.mm"
include "uncom.mm"
include "psseq2i.mm"
include "sylib.mm"

theorem disjpss
  let cA: class A
  let cB: class B


  assert |- ( ( ( A i^i B ) = (/) /\ B =/= (/) ) -> A C. ( A u. B ) )

  proof
    cA
    cB
    cin
    #
    c0
    wceq
    #
    cB
    c0
    wne
    #
    wa
    cB
    cA
    wss
    #
    wn
    #
    cA
    cA
    cB
    cun
    #
    wpss
    #
    @1
    @2
    @4
    @1
    @3
    cB
    c0
    @1
    @3
    cB
    c0
    wss
    #
    cB
    c0
    wceq
    @3
    cB
    @0
    wss
    #
    @1
    @7
    @3
    @3
    cB
    cB
    wss
    #
    wa
    @8
    @9
    @3
    cB
    ssid
    biantru
    cB
    cA
    cB
    ssin
    bitri
    @0
    c0
    cB
    sseq2
    syl5bb
    cB
    ss0
    syl6bi
    necon3ad
    imp
    @4
    cA
    cB
    cA
    cun
    #
    wpss
    @6
    cB
    cA
    nsspssun
    @10
    @5
    cA
    cB
    cA
    uncom
    psseq2i
    bitri
    sylib
end

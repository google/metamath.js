include "wss.mm"
include "wa.mm"
include "cph.mm"
include "co.mm"
include "wceq.mm"
include "ssid.mm"
include "biantrur.mm"
include "shslubi.mm"
include "shsub2i.mm"
include "eqss.mm"
include "mpbiran2.mm"
include "shscomi.mm"
include "sseq1i.mm"
include "bitr2i.mm"
include "3bitri.mm"

theorem shlesb1i
  let cA: class A
  let cB: class B
  let vx: setvar x
  assume shlesb1.1: |- A e. SH
  assume shlesb1.2: |- B e. SH


  assert |- ( A C_ B <-> ( A +H B ) = B )

  proof
    cA
    cB
    wss
    #
    cB
    cB
    wss
    #
    @0
    wa
    cB
    cA
    cph
    co
    #
    cB
    wss
    #
    cA
    cB
    cph
    co
    #
    cB
    wceq
    #
    @1
    @0
    cB
    ssid
    biantrur
    cB
    cA
    cB
    shlesb1.2
    shlesb1.1
    shlesb1.2
    shslubi
    @5
    @4
    cB
    wss
    #
    @3
    @5
    @6
    cB
    @4
    wss
    cB
    cA
    shlesb1.2
    shlesb1.1
    shsub2i
    @4
    cB
    eqss
    mpbiran2
    @4
    @2
    cB
    cA
    cB
    shlesb1.1
    shlesb1.2
    shscomi
    sseq1i
    bitr2i
    3bitri
end

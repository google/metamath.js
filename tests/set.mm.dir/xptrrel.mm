include "cin.mm"
include "c0.mm"
include "wceq.mm"
include "cxp.mm"
include "ccom.mm"
include "wss.mm"
include "cdm.mm"
include "crn.mm"
include "inss1.mm"
include "dmxpss.mm"
include "sstri.mm"
include "inss2.mm"
include "rnxpss.mm"
include "ssini.mm"
include "eqimss.mm"
include "syl5ss.mm"
include "ss0.mm"
include "syl.mm"
include "coemptyd.mm"
include "0ss.mm"
include "syl6eqss.mm"
include "wn.mm"
include "wne.mm"
include "df-ne.mm"
include "biimpri.mm"
include "xpcoidgend.mm"
include "ssid.mm"
include "pm2.61i.mm"

theorem xptrrel
  let cA: class A
  let cB: class B


  assert |- ( ( A X. B ) o. ( A X. B ) ) C_ ( A X. B )

  proof
    cA
    cB
    cin
    #
    c0
    wceq
    #
    cA
    cB
    cxp
    #
    @2
    ccom
    #
    @2
    wss
    @1
    @3
    c0
    @2
    @1
    @2
    @2
    @1
    @2
    cdm
    #
    @2
    crn
    #
    cin
    #
    c0
    wss
    @6
    c0
    wceq
    @1
    @6
    @0
    c0
    @6
    cA
    cB
    @6
    @4
    cA
    @4
    @5
    inss1
    cA
    cB
    dmxpss
    sstri
    @6
    @5
    cB
    @4
    @5
    inss2
    cA
    cB
    rnxpss
    sstri
    ssini
    @0
    c0
    eqimss
    syl5ss
    @6
    ss0
    syl
    coemptyd
    @2
    0ss
    syl6eqss
    @1
    wn
    #
    @3
    @2
    @2
    @7
    cA
    cB
    @0
    c0
    wne
    @7
    @0
    c0
    df-ne
    biimpri
    xpcoidgend
    @2
    ssid
    syl6eqss
    pm2.61i
end

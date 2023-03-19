include "cxp.mm"
include "cdm.mm"
include "wss.mm"
include "c0.mm"
include "wceq.mm"
include "xpeq2.mm"
include "xp0.mm"
include "syl6eq.mm"
include "dmeqd.mm"
include "dm0.mm"
include "0ss.mm"
include "syl6eqss.mm"
include "wne.mm"
include "dmxp.mm"
include "eqimss.mm"
include "syl.mm"
include "pm2.61ine.mm"

theorem dmxpss
  let cA: class A
  let cB: class B


  assert |- dom ( A X. B ) C_ A

  proof
    cA
    cB
    cxp
    #
    cdm
    #
    cA
    wss
    #
    cB
    c0
    cB
    c0
    wceq
    #
    @1
    c0
    cA
    @3
    @1
    c0
    cdm
    c0
    @3
    @0
    c0
    @3
    @0
    cA
    c0
    cxp
    c0
    cB
    c0
    cA
    xpeq2
    cA
    xp0
    syl6eq
    dmeqd
    dm0
    syl6eq
    cA
    0ss
    syl6eqss
    cB
    c0
    wne
    @1
    cA
    wceq
    @2
    cA
    cB
    dmxp
    @1
    cA
    eqimss
    syl
    pm2.61ine
end

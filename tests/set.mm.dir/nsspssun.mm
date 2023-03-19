include "wss.mm"
include "wn.mm"
include "cun.mm"
include "wa.mm"
include "wpss.mm"
include "ssun2.mm"
include "biantrur.mm"
include "ssid.mm"
include "biantru.mm"
include "unss.mm"
include "bitri.mm"
include "xchnxbir.mm"
include "dfpss3.mm"
include "bitr4i.mm"

theorem nsspssun
  let cA: class A
  let cB: class B


  assert |- ( -. A C_ B <-> B C. ( A u. B ) )

  proof
    cA
    cB
    wss
    #
    wn
    cB
    cA
    cB
    cun
    #
    wss
    #
    @1
    cB
    wss
    #
    wn
    #
    wa
    #
    cB
    @1
    wpss
    @3
    @5
    @0
    @2
    @4
    cB
    cA
    ssun2
    biantrur
    @0
    @0
    cB
    cB
    wss
    #
    wa
    @3
    @6
    @0
    cB
    ssid
    biantru
    cA
    cB
    cB
    unss
    bitri
    xchnxbir
    cB
    @1
    dfpss3
    bitr4i
end

include "cpw.mm"
include "wss.mm"
include "c0.mm"
include "wne.mm"
include "wa.mm"
include "cint.mm"
include "cin.mm"
include "wceq.mm"
include "cuni.mm"
include "intssuni2.mm"
include "ssid.mm"
include "sspwuni.mm"
include "mpbi.mm"
include "syl6ss.mm"
include "sseqin2.mm"
include "sylib.mm"

theorem rintn0
  let cA: class A
  let cX: class X


  assert |- ( ( X C_ ~P A /\ X =/= (/) ) -> ( A i^i |^| X ) = |^| X )

  proof
    cX
    cA
    cpw
    #
    wss
    cX
    c0
    wne
    wa
    #
    cX
    cint
    #
    cA
    wss
    cA
    @2
    cin
    @2
    wceq
    @1
    @2
    @0
    cuni
    #
    cA
    cX
    @0
    intssuni2
    @0
    @0
    wss
    @3
    cA
    wss
    @0
    ssid
    @0
    cA
    sspwuni
    mpbi
    syl6ss
    @2
    cA
    sseqin2
    sylib
end

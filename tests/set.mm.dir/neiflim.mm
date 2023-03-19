include "ctopon.mm"
include "cfv.mm"
include "wcel.mm"
include "wa.mm"
include "csn.mm"
include "cnei.mm"
include "cflim.mm"
include "co.mm"
include "wss.mm"
include "ssid.mm"
include "jctr.mm"
include "adantl.mm"
include "cfil.mm"
include "wb.mm"
include "c0.mm"
include "wne.mm"
include "simpl.mm"
include "snssi.mm"
include "snnzg.mm"
include "neifil.mm"
include "syl3anc.mm"
include "elflim.mm"
include "syldan.mm"
include "mpbird.mm"

theorem neiflim
  let cA: class A
  let cJ: class J
  let cX: class X
  let vx: setvar x
  let vy: setvar y
  let cF: class F
  let cG: class G
  let cK: class K


  assert |- ( ( J e. ( TopOn ` X ) /\ A e. X ) -> A e. ( J fLim ( ( nei ` J ) ` { A } ) ) )

  proof
    cJ
    cX
    ctopon
    cfv
    wcel
    #
    cA
    cX
    wcel
    #
    wa
    #
    cA
    cJ
    cA
    csn
    #
    cJ
    cnei
    cfv
    cfv
    #
    cflim
    co
    wcel
    #
    @1
    @4
    @4
    wss
    #
    wa
    #
    @1
    @7
    @0
    @1
    @6
    @4
    ssid
    jctr
    adantl
    @0
    @1
    @4
    cX
    cfil
    cfv
    wcel
    #
    @5
    @7
    wb
    @2
    @0
    @3
    cX
    wss
    #
    @3
    c0
    wne
    #
    @8
    @0
    @1
    simpl
    @1
    @9
    @0
    cA
    cX
    snssi
    adantl
    @1
    @10
    @0
    cA
    cX
    snnzg
    adantl
    @3
    cJ
    cX
    neifil
    syl3anc
    cA
    @4
    cJ
    cX
    elflim
    syldan
    mpbird
end

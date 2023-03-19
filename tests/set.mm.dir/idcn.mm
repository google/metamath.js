include "ctopon.mm"
include "cfv.mm"
include "wcel.mm"
include "cid.mm"
include "cres.mm"
include "ccn.mm"
include "co.mm"
include "wss.mm"
include "ssid.mm"
include "wb.mm"
include "ssidcn.mm"
include "anidms.mm"
include "mpbiri.mm"

theorem idcn
  let cJ: class J
  let cX: class X
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cF: class F
  let cK: class K
  let cP: class P


  assert |- ( J e. ( TopOn ` X ) -> ( _I |` X ) e. ( J Cn J ) )

  proof
    cJ
    cX
    ctopon
    cfv
    wcel
    #
    cid
    cX
    cres
    cJ
    cJ
    ccn
    co
    wcel
    #
    cJ
    cJ
    wss
    #
    cJ
    ssid
    @0
    @1
    @2
    wb
    cJ
    cJ
    cX
    ssidcn
    anidms
    mpbiri
end

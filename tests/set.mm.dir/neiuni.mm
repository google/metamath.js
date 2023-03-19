include "ctop.mm"
include "wcel.mm"
include "wss.mm"
include "wa.mm"
include "cnei.mm"
include "cfv.mm"
include "cuni.mm"
include "tpnei.mm"
include "biimpa.mm"
include "elssuni.mm"
include "syl.mm"
include "cv.mm"
include "wral.mm"
include "wi.mm"
include "neii1.mm"
include "ex.mm"
include "adantr.mm"
include "ralrimiv.mm"
include "unissb.mm"
include "sylibr.mm"
include "eqssd.mm"

theorem neiuni
  let cS: class S
  let cJ: class J
  let cX: class X
  let vx: setvar x
  let vn: setvar n
  let cK: class K
  let cP: class P
  let cY: class Y
  assume tpnei.1: |- X = U. J


  assert |- ( ( J e. Top /\ S C_ X ) -> X = U. ( ( nei ` J ) ` S ) )

  proof
    cJ
    ctop
    wcel
    #
    cS
    cX
    wss
    #
    wa
    #
    cX
    cS
    cJ
    cnei
    cfv
    cfv
    #
    cuni
    #
    @2
    cX
    @3
    wcel
    #
    cX
    @4
    wss
    @0
    @1
    @5
    cS
    cJ
    cX
    tpnei.1
    tpnei
    biimpa
    cX
    @3
    elssuni
    syl
    @2
    vx
    cv
    #
    cX
    wss
    #
    vx
    @3
    wral
    @4
    cX
    wss
    @2
    @7
    vx
    @3
    @0
    @6
    @3
    wcel
    #
    @7
    wi
    @1
    @0
    @8
    @7
    cS
    cJ
    @6
    cX
    tpnei.1
    neii1
    ex
    adantr
    ralrimiv
    vx
    @3
    cX
    unissb
    sylibr
    eqssd
end

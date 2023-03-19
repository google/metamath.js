include "ctop.mm"
include "wcel.mm"
include "wss.mm"
include "cnei.mm"
include "cfv.mm"
include "wi.mm"
include "topopn.mm"
include "opnneiss.mm"
include "3exp.mm"
include "mpd.mm"
include "ssnei.mm"
include "ex.mm"
include "impbid.mm"

theorem tpnei
  let cS: class S
  let cJ: class J
  let cX: class X
  let vx: setvar x
  let vn: setvar n
  let cK: class K
  let cP: class P
  let cY: class Y
  assume tpnei.1: |- X = U. J


  assert |- ( J e. Top -> ( S C_ X <-> X e. ( ( nei ` J ) ` S ) ) )

  proof
    cJ
    ctop
    wcel
    #
    cS
    cX
    wss
    #
    cX
    cS
    cJ
    cnei
    cfv
    cfv
    wcel
    #
    @0
    cX
    cJ
    wcel
    #
    @1
    @2
    wi
    cJ
    cX
    tpnei.1
    topopn
    @0
    @3
    @1
    @2
    cS
    cJ
    cX
    opnneiss
    3exp
    mpd
    @0
    @2
    @1
    cS
    cJ
    cX
    ssnei
    ex
    impbid
end

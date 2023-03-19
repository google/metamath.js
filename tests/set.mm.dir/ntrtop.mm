include "ctop.mm"
include "wcel.mm"
include "cnt.mm"
include "cfv.mm"
include "wceq.mm"
include "topopn.mm"
include "wss.mm"
include "wb.mm"
include "ssid.mm"
include "isopn3.mm"
include "mpan2.mm"
include "mpbid.mm"

theorem ntrtop
  let cJ: class J
  let cX: class X
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cP: class P
  let cS: class S
  let cU: class U
  let cT: class T
  let cA: class A
  assume clscld.1: |- X = U. J


  assert |- ( J e. Top -> ( ( int ` J ) ` X ) = X )

  proof
    cJ
    ctop
    wcel
    #
    cX
    cJ
    wcel
    #
    cX
    cJ
    cnt
    cfv
    cfv
    cX
    wceq
    #
    cJ
    cX
    clscld.1
    topopn
    @0
    cX
    cX
    wss
    @1
    @2
    wb
    cX
    ssid
    cX
    cJ
    cX
    clscld.1
    isopn3
    mpan2
    mpbid
end

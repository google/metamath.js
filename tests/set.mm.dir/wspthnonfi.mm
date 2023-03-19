include "cvtx.mm"
include "cfv.mm"
include "cfn.mm"
include "wcel.mm"
include "cwwlksnon.mm"
include "co.mm"
include "cwwspthsnon.mm"
include "wwlksnonfi.mm"
include "wss.mm"
include "wspthsswwlknon.mm"
include "a1i.mm"
include "ssfid.mm"

theorem wspthnonfi
  let cA: class A
  let cB: class B
  let cG: class G
  let cN: class N


  assert |- ( ( Vtx ` G ) e. Fin -> ( A ( N WSPathsNOn G ) B ) e. Fin )

  proof
    cG
    cvtx
    cfv
    cfn
    wcel
    #
    cA
    cB
    cN
    cG
    cwwlksnon
    co
    co
    #
    cA
    cB
    cN
    cG
    cwwspthsnon
    co
    co
    #
    cA
    cB
    cG
    cN
    wwlksnonfi
    @2
    @1
    wss
    @0
    cA
    cB
    cG
    cN
    wspthsswwlknon
    a1i
    ssfid
end

include "cvtx.mm"
include "cfv.mm"
include "cfn.mm"
include "wcel.mm"
include "cwwlksn.mm"
include "co.mm"
include "cwwspthsn.mm"
include "wwlksnfi.mm"
include "wss.mm"
include "wspthsswwlkn.mm"
include "a1i.mm"
include "ssfid.mm"

theorem wspthnfi
  let cG: class G
  let cN: class N


  assert |- ( ( Vtx ` G ) e. Fin -> ( N WSPathsN G ) e. Fin )

  proof
    cG
    cvtx
    cfv
    cfn
    wcel
    #
    cN
    cG
    cwwlksn
    co
    #
    cN
    cG
    cwwspthsn
    co
    #
    cG
    cN
    wwlksnfi
    @2
    @1
    wss
    @0
    cG
    cN
    wspthsswwlkn
    a1i
    ssfid
end

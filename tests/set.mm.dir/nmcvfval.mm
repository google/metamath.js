include "cnmcv.mm"
include "cfv.mm"
include "c2nd.mm"
include "df-nmcv.mm"
include "fveq1i.mm"
include "eqtri.mm"

theorem nmcvfval
  let cU: class U
  let cN: class N
  assume nmfval.6: |- N = ( normCV ` U )


  assert |- N = ( 2nd ` U )

  proof
    cN
    cU
    cnmcv
    cfv
    cU
    c2nd
    cfv
    nmfval.6
    cU
    cnmcv
    c2nd
    df-nmcv
    fveq1i
    eqtri
end

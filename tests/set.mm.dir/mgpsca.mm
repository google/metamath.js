include "csca.mm"
include "cfv.mm"
include "c5.mm"
include "df-sca.mm"
include "5nn.mm"
include "c2.mm"
include "2re.mm"
include "2lt5.mm"
include "gtneii.mm"
include "mgplem.mm"
include "eqtri.mm"

theorem mgpsca
  let cR: class R
  let cS: class S
  let cM: class M
  assume mgpbas.1: |- M = ( mulGrp ` R )
  assume mgpsca.s: |- S = ( Scalar ` R )


  assert |- S = ( Scalar ` M )

  proof
    cS
    cR
    csca
    cfv
    cM
    csca
    cfv
    mgpsca.s
    cR
    csca
    cM
    c5
    mgpbas.1
    df-sca
    5nn
    c2
    c5
    2re
    2lt5
    gtneii
    mgplem
    eqtri
end

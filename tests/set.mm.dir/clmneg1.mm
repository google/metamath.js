include "cclm.mm"
include "wcel.mm"
include "cz.mm"
include "wss.mm"
include "c1.mm"
include "cneg.mm"
include "clmzss.mm"
include "neg1z.mm"
include "ssel.mm"
include "mpisyl.mm"

theorem clmneg1
  let cF: class F
  let cK: class K
  let cW: class W
  assume clm0.f: |- F = ( Scalar ` W )
  assume clmsub.k: |- K = ( Base ` F )


  assert |- ( W e. CMod -> -u 1 e. K )

  proof
    cW
    cclm
    wcel
    cz
    cK
    wss
    c1
    cneg
    #
    cz
    wcel
    @0
    cK
    wcel
    cF
    cK
    cW
    clm0.f
    clmsub.k
    clmzss
    neg1z
    cz
    cK
    @0
    ssel
    mpisyl
end

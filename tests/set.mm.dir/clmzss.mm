include "cclm.mm"
include "wcel.mm"
include "ccnfld.mm"
include "csubrg.mm"
include "cfv.mm"
include "cz.mm"
include "wss.mm"
include "clmsubrg.mm"
include "zsssubrg.mm"
include "syl.mm"

theorem clmzss
  let cF: class F
  let cK: class K
  let cW: class W
  assume clm0.f: |- F = ( Scalar ` W )
  assume clmsub.k: |- K = ( Base ` F )


  assert |- ( W e. CMod -> ZZ C_ K )

  proof
    cW
    cclm
    wcel
    cK
    ccnfld
    csubrg
    cfv
    wcel
    cz
    cK
    wss
    cF
    cK
    cW
    clm0.f
    clmsub.k
    clmsubrg
    cK
    zsssubrg
    syl
end

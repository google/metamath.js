include "cclm.mm"
include "wcel.mm"
include "ccnfld.mm"
include "csubrg.mm"
include "cfv.mm"
include "cc.mm"
include "wss.mm"
include "clmsubrg.mm"
include "cnfldbas.mm"
include "subrgss.mm"
include "syl.mm"

theorem clmsscn
  let cF: class F
  let cK: class K
  let cW: class W
  assume clm0.f: |- F = ( Scalar ` W )
  assume clmsub.k: |- K = ( Base ` F )


  assert |- ( W e. CMod -> K C_ CC )

  proof
    cW
    cclm
    wcel
    cK
    ccnfld
    csubrg
    cfv
    wcel
    cK
    cc
    wss
    cF
    cK
    cW
    clm0.f
    clmsub.k
    clmsubrg
    cK
    cc
    ccnfld
    cnfldbas
    subrgss
    syl
end

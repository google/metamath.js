include "cclm.mm"
include "wcel.mm"
include "ccnfld.mm"
include "csubrg.mm"
include "cfv.mm"
include "caddc.mm"
include "co.mm"
include "clmsubrg.mm"
include "cnfldadd.mm"
include "subrgacl.mm"
include "syl3an1.mm"

theorem clmacl
  let cF: class F
  let cK: class K
  let cW: class W
  let cX: class X
  let cY: class Y
  assume clm0.f: |- F = ( Scalar ` W )
  assume clmsub.k: |- K = ( Base ` F )


  assert |- ( ( W e. CMod /\ X e. K /\ Y e. K ) -> ( X + Y ) e. K )

  proof
    cW
    cclm
    wcel
    cK
    ccnfld
    csubrg
    cfv
    wcel
    cX
    cK
    wcel
    cY
    cK
    wcel
    cX
    cY
    caddc
    co
    cK
    wcel
    cF
    cK
    cW
    clm0.f
    clmsub.k
    clmsubrg
    cK
    caddc
    ccnfld
    cX
    cY
    cnfldadd
    subrgacl
    syl3an1
end

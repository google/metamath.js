include "cclm.mm"
include "wcel.mm"
include "ccnfld.mm"
include "csubg.mm"
include "cfv.mm"
include "cmin.mm"
include "co.mm"
include "csubrg.mm"
include "clmsubrg.mm"
include "subrgsubg.mm"
include "syl.mm"
include "cnfldsub.mm"
include "subgsubcl.mm"
include "syl3an1.mm"

theorem clmsubcl
  let cF: class F
  let cK: class K
  let cW: class W
  let cX: class X
  let cY: class Y
  assume clm0.f: |- F = ( Scalar ` W )
  assume clmsub.k: |- K = ( Base ` F )


  assert |- ( ( W e. CMod /\ X e. K /\ Y e. K ) -> ( X - Y ) e. K )

  proof
    cW
    cclm
    wcel
    #
    cK
    ccnfld
    csubg
    cfv
    wcel
    #
    cX
    cK
    wcel
    cY
    cK
    wcel
    cX
    cY
    cmin
    co
    cK
    wcel
    @0
    cK
    ccnfld
    csubrg
    cfv
    wcel
    @1
    cF
    cK
    cW
    clm0.f
    clmsub.k
    clmsubrg
    cK
    ccnfld
    subrgsubg
    syl
    cK
    ccnfld
    cmin
    cX
    cY
    cnfldsub
    subgsubcl
    syl3an1
end

include "cword.mm"
include "wcel.mm"
include "c1.mm"
include "chash.mm"
include "cfv.mm"
include "cle.mm"
include "wbr.mm"
include "cc0.mm"
include "cfzo.mm"
include "co.mm"
include "wa.mm"
include "cn.mm"
include "cn0.mm"
include "lencl.mm"
include "elnnnn0c.mm"
include "biimpri.mm"
include "sylan.mm"
include "lbfzo0.mm"
include "sylibr.mm"
include "wrdsymbcl.mm"
include "syldan.mm"

theorem wrdsymb1
  let cV: class V
  let cW: class W


  assert |- ( ( W e. Word V /\ 1 <_ ( # ` W ) ) -> ( W ` 0 ) e. V )

  proof
    cW
    cV
    cword
    wcel
    #
    c1
    cW
    chash
    cfv
    #
    cle
    wbr
    #
    cc0
    cc0
    @1
    cfzo
    co
    wcel
    #
    cc0
    cW
    cfv
    cV
    wcel
    @0
    @2
    wa
    @1
    cn
    wcel
    #
    @3
    @0
    @1
    cn0
    wcel
    #
    @2
    @4
    cV
    cW
    lencl
    @4
    @5
    @2
    wa
    @1
    elnnnn0c
    biimpri
    sylan
    @1
    lbfzo0
    sylibr
    cc0
    cV
    cW
    wrdsymbcl
    syldan
end

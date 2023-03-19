include "cword.mm"
include "wcel.mm"
include "chash.mm"
include "cfv.mm"
include "cn.mm"
include "c0.mm"
include "wne.mm"
include "cfn.mm"
include "wb.mm"
include "wrdfin.mm"
include "hashnncl.mm"
include "syl.mm"
include "biimpar.mm"

theorem lennncl
  let cS: class S
  let cW: class W


  assert |- ( ( W e. Word S /\ W =/= (/) ) -> ( # ` W ) e. NN )

  proof
    cW
    cS
    cword
    wcel
    #
    cW
    chash
    cfv
    cn
    wcel
    #
    cW
    c0
    wne
    #
    @0
    cW
    cfn
    wcel
    @1
    @2
    wb
    cS
    cW
    wrdfin
    cW
    hashnncl
    syl
    biimpar
end

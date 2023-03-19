include "cword.mm"
include "wcel.mm"
include "c0.mm"
include "wne.mm"
include "cc0.mm"
include "cfv.mm"
include "c1.mm"
include "chash.mm"
include "cle.mm"
include "wbr.mm"
include "wrdlenge1n0.mm"
include "wrdsymb1.mm"
include "ex.mm"
include "sylbid.mm"
include "imp.mm"

theorem fstwrdne
  let cV: class V
  let cW: class W


  assert |- ( ( W e. Word V /\ W =/= (/) ) -> ( W ` 0 ) e. V )

  proof
    cW
    cV
    cword
    wcel
    #
    cW
    c0
    wne
    #
    cc0
    cW
    cfv
    cV
    wcel
    #
    @0
    @1
    c1
    cW
    chash
    cfv
    cle
    wbr
    #
    @2
    cV
    cW
    wrdlenge1n0
    @0
    @3
    @2
    cV
    cW
    wrdsymb1
    ex
    sylbid
    imp
end

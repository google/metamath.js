include "cword.mm"
include "wcel.mm"
include "c0.mm"
include "wne.mm"
include "chash.mm"
include "cfv.mm"
include "cn.mm"
include "lennncl.mm"
include "ex.mm"
include "c1.mm"
include "cle.mm"
include "wbr.mm"
include "nnge1.mm"
include "wrdlenge1n0.mm"
include "syl5ibr.mm"
include "impbid.mm"

theorem len0nnbi
  let cS: class S
  let cW: class W


  assert |- ( W e. Word S -> ( W =/= (/) <-> ( # ` W ) e. NN ) )

  proof
    cW
    cS
    cword
    wcel
    #
    cW
    c0
    wne
    #
    cW
    chash
    cfv
    #
    cn
    wcel
    #
    @0
    @1
    @3
    cS
    cW
    lennncl
    ex
    @3
    @1
    @0
    c1
    @2
    cle
    wbr
    @2
    nnge1
    cS
    cW
    wrdlenge1n0
    syl5ibr
    impbid
end

include "cclwwlk.mm"
include "cfv.mm"
include "wcel.mm"
include "cvv.mm"
include "cvtx.mm"
include "cword.mm"
include "c0.mm"
include "wne.mm"
include "w3a.mm"
include "cc0.mm"
include "chash.mm"
include "clt.mm"
include "wbr.mm"
include "eqid.mm"
include "clwwlkbp.mm"
include "hashneq0.mm"
include "biimpar.mm"
include "3adant1.mm"
include "syl.mm"

theorem clwwlkgt0
  let cG: class G
  let cW: class W


  assert |- ( W e. ( ClWWalks ` G ) -> 0 < ( # ` W ) )

  proof
    cW
    cG
    cclwwlk
    cfv
    wcel
    cG
    cvv
    wcel
    #
    cW
    cG
    cvtx
    cfv
    #
    cword
    #
    wcel
    #
    cW
    c0
    wne
    #
    w3a
    cc0
    cW
    chash
    cfv
    clt
    wbr
    #
    cG
    @1
    cW
    @1
    eqid
    clwwlkbp
    @3
    @4
    @5
    @0
    @3
    @5
    @4
    cW
    @2
    hashneq0
    biimpar
    3adant1
    syl
end

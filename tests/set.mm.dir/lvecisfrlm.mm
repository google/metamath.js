include "clvec.mm"
include "wcel.mm"
include "clbs.mm"
include "cfv.mm"
include "c0.mm"
include "wne.mm"
include "cv.mm"
include "cfrlm.mm"
include "co.mm"
include "clmic.mm"
include "wbr.mm"
include "wex.mm"
include "eqid.mm"
include "lbsex.mm"
include "clmod.mm"
include "wb.mm"
include "lveclmod.mm"
include "lmisfree.mm"
include "syl.mm"
include "mpbid.mm"

theorem lvecisfrlm
  let vk: setvar k
  let cF: class F
  let cW: class W
  assume lvecisfrlm.f: |- F = ( Scalar ` W )

  disjoint F k
  disjoint W k
  assert |- ( W e. LVec -> E. k W ~=m ( F freeLMod k ) )

  proof
    cW
    clvec
    wcel
    #
    cW
    clbs
    cfv
    #
    c0
    wne
    #
    cW
    cF
    vk
    cv
    cfrlm
    co
    clmic
    wbr
    vk
    wex
    #
    @1
    cW
    @1
    eqid
    #
    lbsex
    @0
    cW
    clmod
    wcel
    @2
    @3
    wb
    cW
    lveclmod
    vk
    cF
    @1
    cW
    @4
    lvecisfrlm.f
    lmisfree
    syl
    mpbid
end

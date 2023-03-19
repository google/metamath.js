include "cwlks.mm"
include "cfv.mm"
include "wbr.mm"
include "c1.mm"
include "cewlks.mm"
include "co.mm"
include "wcel.mm"
include "ciedg.mm"
include "cdm.mm"
include "cword.mm"
include "cv.mm"
include "cmin.mm"
include "cin.mm"
include "chash.mm"
include "cle.mm"
include "cfzo.mm"
include "wral.mm"
include "eqid.mm"
include "wlkf.mm"
include "wlk1walk.mm"
include "cvv.mm"
include "cxnn0.mm"
include "wa.mm"
include "wb.mm"
include "wlkv.mm"
include "simp1d.mm"
include "cn0.mm"
include "1nn0.mm"
include "nn0xnn0.mm"
include "mp1i.mm"
include "isewlk.mm"
include "syl3anc.mm"
include "mpbir2and.mm"

theorem wlk1ewlk
  let cP: class P
  let cF: class F
  let cG: class G
  let vk: setvar k


  assert |- ( F ( Walks ` G ) P -> F e. ( G EdgWalks 1 ) )

  proof
    cF
    cP
    cG
    cwlks
    cfv
    wbr
    #
    cF
    cG
    c1
    cewlks
    co
    wcel
    #
    cF
    cG
    ciedg
    cfv
    #
    cdm
    cword
    #
    wcel
    #
    c1
    vk
    cv
    #
    c1
    cmin
    co
    cF
    cfv
    @2
    cfv
    @5
    cF
    cfv
    @2
    cfv
    cin
    chash
    cfv
    cle
    wbr
    vk
    c1
    cF
    chash
    cfv
    cfzo
    co
    wral
    #
    cP
    cF
    cG
    @2
    @2
    eqid
    #
    wlkf
    #
    cP
    vk
    cF
    cG
    @2
    @7
    wlk1walk
    @0
    cG
    cvv
    wcel
    #
    c1
    cxnn0
    wcel
    #
    @4
    @1
    @4
    @6
    wa
    wb
    @0
    @9
    cF
    cvv
    wcel
    cP
    cvv
    wcel
    cP
    cF
    cG
    wlkv
    simp1d
    c1
    cn0
    wcel
    @10
    @0
    1nn0
    c1
    nn0xnn0
    mp1i
    @8
    c1
    @3
    vk
    cF
    cG
    @2
    cvv
    @7
    isewlk
    syl3anc
    mpbir2and
end

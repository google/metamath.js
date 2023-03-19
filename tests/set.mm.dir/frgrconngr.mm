include "cfrgr.mm"
include "wcel.mm"
include "cconngr.mm"
include "cv.mm"
include "cpthson.mm"
include "cfv.mm"
include "co.mm"
include "wbr.mm"
include "wex.mm"
include "cvtx.mm"
include "csn.mm"
include "cdif.mm"
include "wral.mm"
include "cspthson.mm"
include "chash.mm"
include "c2.mm"
include "wceq.mm"
include "wa.mm"
include "eqid.mm"
include "2pthfrgr.mm"
include "spthonpthon.mm"
include "adantr.mm"
include "2eximi.mm"
include "2ralimi.mm"
include "syl.mm"
include "isconngr1.mm"
include "mpbird.mm"

theorem frgrconngr
  let cG: class G
  let vf: setvar f
  let vk: setvar k
  let vn: setvar n
  let vp: setvar p


  assert |- ( G e. FriendGraph -> G e. ConnGraph )

  proof
    cG
    cfrgr
    wcel
    #
    cG
    cconngr
    wcel
    vf
    cv
    #
    vp
    cv
    #
    vk
    cv
    #
    vn
    cv
    #
    cG
    cpthson
    cfv
    co
    wbr
    #
    vp
    wex
    vf
    wex
    #
    vn
    cG
    cvtx
    cfv
    #
    @3
    csn
    cdif
    #
    wral
    vk
    @7
    wral
    #
    @0
    @1
    @2
    @3
    @4
    cG
    cspthson
    cfv
    co
    wbr
    #
    @1
    chash
    cfv
    c2
    wceq
    #
    wa
    #
    vp
    wex
    vf
    wex
    #
    vn
    @8
    wral
    vk
    @7
    wral
    @9
    vf
    cG
    @7
    vp
    vk
    vn
    @7
    eqid
    #
    2pthfrgr
    @13
    @6
    vk
    vn
    @7
    @8
    @12
    @5
    vf
    vp
    @10
    @5
    @11
    @3
    @4
    @2
    @1
    cG
    spthonpthon
    adantr
    2eximi
    2ralimi
    syl
    vf
    vk
    vn
    cG
    @7
    cfrgr
    vp
    @14
    isconngr1
    mpbird
end

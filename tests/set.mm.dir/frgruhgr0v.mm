include "cuhgr.mm"
include "wcel.mm"
include "cvtx.mm"
include "cfv.mm"
include "c0.mm"
include "wceq.mm"
include "ciedg.mm"
include "cfrgr.mm"
include "wa.mm"
include "uhgr0vb.mm"
include "biimpcd.mm"
include "anabsi5.mm"
include "frgr0vb.mm"
include "mpd3an3.mm"

theorem frgruhgr0v
  let cG: class G
  let vk: setvar k
  let vl: setvar l
  let vx: setvar x


  assert |- ( ( G e. UHGraph /\ ( Vtx ` G ) = (/) ) -> G e. FriendGraph )

  proof
    cG
    cuhgr
    wcel
    #
    cG
    cvtx
    cfv
    c0
    wceq
    #
    cG
    ciedg
    cfv
    c0
    wceq
    #
    cG
    cfrgr
    wcel
    @0
    @1
    @2
    @0
    @1
    wa
    @0
    @2
    cG
    cuhgr
    uhgr0vb
    biimpcd
    anabsi5
    cG
    cuhgr
    frgr0vb
    mpd3an3
end

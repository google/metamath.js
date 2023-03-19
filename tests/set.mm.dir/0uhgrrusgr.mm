include "cuhgr.mm"
include "wcel.mm"
include "cvtx.mm"
include "cfv.mm"
include "c0.mm"
include "wceq.mm"
include "ciedg.mm"
include "cv.mm"
include "crusgr.mm"
include "wbr.mm"
include "cxnn0.mm"
include "wral.mm"
include "wi.mm"
include "wa.mm"
include "uhgr0vb.mm"
include "biimpd.mm"
include "ex.mm"
include "pm2.43a.mm"
include "imp.mm"
include "0vtxrusgr.mm"
include "mpd3an3.mm"

theorem 0uhgrrusgr
  let vk: setvar k
  let cG: class G
  let vv: setvar v
  let cW: class W

  disjoint G k
  disjoint G v
  disjoint k v
  disjoint W k
  disjoint W v
  assert |- ( ( G e. UHGraph /\ ( Vtx ` G ) = (/) ) -> A. k e. NN0* G RegUSGraph k )

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
    vk
    cv
    crusgr
    wbr
    vk
    cxnn0
    wral
    @0
    @1
    @2
    @1
    @0
    @2
    @0
    @1
    @0
    @2
    wi
    @0
    @1
    wa
    @0
    @2
    cG
    cuhgr
    uhgr0vb
    biimpd
    ex
    pm2.43a
    imp
    vk
    cG
    cuhgr
    0vtxrusgr
    mpd3an3
end

include "cfbas.mm"
include "cfv.mm"
include "wcel.mm"
include "c0.mm"
include "wn.mm"
include "wne.mm"
include "0nelfb.mm"
include "wceq.mm"
include "fveq2.mm"
include "eleq2d.mm"
include "biimpd.mm"
include "cv.mm"
include "wex.mm"
include "fbasne0.mm"
include "n0.mm"
include "sylib.mm"
include "wa.mm"
include "wss.mm"
include "fbelss.mm"
include "ss0.mm"
include "syl.mm"
include "simpr.mm"
include "eqeltrrd.mm"
include "exlimddv.mm"
include "syl6com.mm"
include "necon3bd.mm"
include "mpd.mm"

theorem fbdmn0
  let cB: class B
  let cF: class F
  let vx: setvar x
  let vy: setvar y


  assert |- ( F e. ( fBas ` B ) -> B =/= (/) )

  proof
    cF
    cB
    cfbas
    cfv
    #
    wcel
    #
    c0
    cF
    wcel
    #
    wn
    cB
    c0
    wne
    cB
    cF
    0nelfb
    @1
    @2
    cB
    c0
    cB
    c0
    wceq
    #
    @1
    cF
    c0
    cfbas
    cfv
    #
    wcel
    #
    @2
    @3
    @1
    @5
    @3
    @0
    @4
    cF
    cB
    c0
    cfbas
    fveq2
    eleq2d
    biimpd
    @5
    vx
    cv
    #
    cF
    wcel
    #
    @2
    vx
    @5
    cF
    c0
    wne
    @7
    vx
    wex
    c0
    cF
    fbasne0
    vx
    cF
    n0
    sylib
    @5
    @7
    wa
    #
    @6
    c0
    cF
    @8
    @6
    c0
    wss
    @6
    c0
    wceq
    c0
    cF
    @6
    fbelss
    @6
    ss0
    syl
    @5
    @7
    simpr
    eqeltrrd
    exlimddv
    syl6com
    necon3bd
    mpd
end

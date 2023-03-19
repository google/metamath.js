include "cwlks.mm"
include "cfv.mm"
include "c0.mm"
include "wceq.mm"
include "cvtx.mm"
include "wi.mm"
include "ax-1.mm"
include "wn.mm"
include "cv.mm"
include "wcel.mm"
include "wex.mm"
include "neq0.mm"
include "wa.mm"
include "c1st.mm"
include "c2nd.mm"
include "wlkv0.mm"
include "wbr.mm"
include "wlkcpr.mm"
include "wne.mm"
include "wlkn0.mm"
include "eqneqall.mm"
include "adantl.mm"
include "syl5com.mm"
include "sylbi.mm"
include "mpd.mm"
include "expcom.mm"
include "exlimiv.mm"
include "pm2.61i.mm"

theorem g0wlk0
  let cG: class G
  let vw: setvar w


  assert |- ( ( Vtx ` G ) = (/) -> ( Walks ` G ) = (/) )

  proof
    cG
    cwlks
    cfv
    #
    c0
    wceq
    #
    cG
    cvtx
    cfv
    c0
    wceq
    #
    @1
    wi
    #
    @1
    @2
    ax-1
    @1
    wn
    vw
    cv
    #
    @0
    wcel
    #
    vw
    wex
    @3
    vw
    @0
    neq0
    @5
    @3
    vw
    @2
    @5
    @1
    @2
    @5
    wa
    @4
    c1st
    cfv
    #
    c0
    wceq
    #
    @4
    c2nd
    cfv
    #
    c0
    wceq
    #
    wa
    #
    @1
    cG
    @4
    wlkv0
    @5
    @10
    @1
    wi
    #
    @2
    @5
    @6
    @8
    @0
    wbr
    #
    @11
    cG
    @4
    wlkcpr
    @12
    @8
    c0
    wne
    #
    @10
    @1
    @8
    @6
    cG
    wlkn0
    @9
    @13
    @1
    wi
    @7
    @1
    @8
    c0
    eqneqall
    adantl
    syl5com
    sylbi
    adantl
    mpd
    expcom
    exlimiv
    sylbi
    pm2.61i
end

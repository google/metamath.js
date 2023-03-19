include "cc.mm"
include "wcel.mm"
include "cc0.mm"
include "wne.mm"
include "c1.mm"
include "w3a.mm"
include "clogb.mm"
include "ccur.mm"
include "cfv.mm"
include "csn.mm"
include "cdif.mm"
include "cv.mm"
include "clog.mm"
include "cdiv.mm"
include "co.mm"
include "csb.mm"
include "cmpt.mm"
include "cvv.mm"
include "cpr.mm"
include "df-logb.mm"
include "wa.mm"
include "ovexd.mm"
include "ralrimivva.mm"
include "c0.mm"
include "wn.mm"
include "ax-1cn.mm"
include "ax-1ne0.mm"
include "wceq.mm"
include "wb.mm"
include "elsng.mm"
include "ax-mp.mm"
include "nemtbir.mm"
include "eldif.mm"
include "mpbir2an.mm"
include "ne0ii.mm"
include "a1i.mm"
include "cnex.mm"
include "difexg.mm"
include "eldifpr.mm"
include "biimpri.mm"
include "mpt2curryvald.mm"
include "csbov2g.mm"
include "csbfv.mm"
include "oveq2d.mm"
include "eqtrd.mm"
include "3ad2ant1.mm"
include "mpteq2dv.mm"

theorem logbmpt
  let vy: setvar y
  let cB: class B
  let vx: setvar x

  disjoint B y
  disjoint B x
  disjoint x y
  assert |- ( ( B e. CC /\ B =/= 0 /\ B =/= 1 ) -> ( curry logb ` B ) = ( y e. ( CC \ { 0 } ) |-> ( ( log ` y ) / ( log ` B ) ) ) )

  proof
    cB
    cc
    wcel
    #
    cB
    cc0
    wne
    #
    cB
    c1
    wne
    #
    w3a
    #
    cB
    clogb
    ccur
    cfv
    vy
    cc
    cc0
    csn
    #
    cdif
    #
    vx
    cB
    vy
    cv
    #
    clog
    cfv
    #
    vx
    cv
    #
    clog
    cfv
    #
    cdiv
    co
    #
    csb
    #
    cmpt
    vy
    @5
    @7
    cB
    clog
    cfv
    #
    cdiv
    co
    #
    cmpt
    @3
    vx
    vy
    cB
    @10
    clogb
    cvv
    cvv
    cc
    cc0
    c1
    cpr
    cdif
    #
    @5
    vx
    vy
    df-logb
    @3
    @10
    cvv
    wcel
    vx
    vy
    @14
    @5
    @3
    @8
    @14
    wcel
    @6
    @5
    wcel
    wa
    wa
    @7
    @9
    cdiv
    ovexd
    ralrimivva
    @5
    c0
    wne
    @3
    c1
    @5
    c1
    @5
    wcel
    c1
    cc
    wcel
    #
    c1
    @4
    wcel
    #
    wn
    ax-1cn
    @16
    c1
    cc0
    ax-1ne0
    @15
    @16
    c1
    cc0
    wceq
    wb
    ax-1cn
    c1
    cc0
    cc
    elsng
    ax-mp
    nemtbir
    c1
    cc
    @4
    eldif
    mpbir2an
    ne0ii
    a1i
    @5
    cvv
    wcel
    #
    @3
    cc
    cvv
    wcel
    @17
    cnex
    cc
    @4
    cvv
    difexg
    ax-mp
    a1i
    cB
    @14
    wcel
    @3
    cB
    cc
    cc0
    c1
    eldifpr
    biimpri
    mpt2curryvald
    @3
    vy
    @5
    @11
    @13
    @0
    @1
    @11
    @13
    wceq
    @2
    @0
    @11
    @7
    vx
    cB
    @9
    csb
    #
    cdiv
    co
    @13
    vx
    cB
    @7
    @9
    cdiv
    cc
    csbov2g
    @0
    @18
    @12
    @7
    cdiv
    @18
    @12
    wceq
    @0
    vx
    cB
    clog
    csbfv
    a1i
    oveq2d
    eqtrd
    3ad2ant1
    mpteq2dv
    eqtrd
end

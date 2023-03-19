include "wcel.mm"
include "c2o.mm"
include "cmap.mm"
include "co.mm"
include "c0.mm"
include "csn.mm"
include "c1o.mm"
include "cxp.mm"
include "cen.mm"
include "wbr.mm"
include "cun.mm"
include "cpr.mm"
include "df2o3.mm"
include "df-pr.mm"
include "eqtri.mm"
include "oveq2i.mm"
include "cvv.mm"
include "cin.mm"
include "wceq.mm"
include "snex.mm"
include "a1i.mm"
include "id.mm"
include "wn.mm"
include "1n0.mm"
include "neii.mm"
include "elsni.mm"
include "mto.mm"
include "disjsn.mm"
include "mpbir.mm"
include "mapunen.mm"
include "syl31anc.mm"
include "syl5eqbr.mm"
include "cv.mm"
include "oveq1.mm"
include "breq12d.mm"
include "vex.mm"
include "0ex.mm"
include "mapsnen.mm"
include "vtoclg.mm"
include "df1o2.mm"
include "eqeltri.mm"
include "xpen.mm"
include "syl2anc.mm"
include "entr.mm"

theorem map2xp
  let cA: class A
  let cV: class V
  let vx: setvar x


  assert |- ( A e. V -> ( A ^m 2o ) ~~ ( A X. A ) )

  proof
    cA
    cV
    wcel
    #
    cA
    c2o
    cmap
    co
    #
    cA
    c0
    csn
    #
    cmap
    co
    #
    cA
    c1o
    csn
    #
    cmap
    co
    #
    cxp
    #
    cen
    wbr
    @6
    cA
    cA
    cxp
    #
    cen
    wbr
    #
    @1
    @7
    cen
    wbr
    @0
    @1
    cA
    @2
    @4
    cun
    #
    cmap
    co
    #
    @6
    cen
    c2o
    @9
    cA
    cmap
    c2o
    c0
    c1o
    cpr
    @9
    df2o3
    c0
    c1o
    df-pr
    eqtri
    oveq2i
    @0
    @2
    cvv
    wcel
    #
    @4
    cvv
    wcel
    #
    @0
    @2
    @4
    cin
    c0
    wceq
    #
    @10
    @6
    cen
    wbr
    @11
    @0
    c0
    snex
    #
    a1i
    @12
    @0
    c1o
    snex
    a1i
    @0
    id
    @13
    @0
    @13
    c1o
    @2
    wcel
    #
    wn
    @15
    c1o
    c0
    wceq
    c1o
    c0
    1n0
    neii
    c1o
    c0
    elsni
    mto
    @2
    c1o
    disjsn
    mpbir
    a1i
    @2
    @4
    cA
    cvv
    cvv
    cV
    mapunen
    syl31anc
    syl5eqbr
    @0
    @3
    cA
    cen
    wbr
    #
    @5
    cA
    cen
    wbr
    #
    @8
    vx
    cv
    #
    @2
    cmap
    co
    #
    @18
    cen
    wbr
    @16
    vx
    cA
    cV
    @18
    cA
    wceq
    #
    @19
    @3
    @18
    cA
    cen
    @18
    cA
    @2
    cmap
    oveq1
    @20
    id
    #
    breq12d
    @18
    c0
    vx
    vex
    #
    0ex
    mapsnen
    vtoclg
    @18
    @4
    cmap
    co
    #
    @18
    cen
    wbr
    @17
    vx
    cA
    cV
    @20
    @23
    @5
    @18
    cA
    cen
    @18
    cA
    @4
    cmap
    oveq1
    @21
    breq12d
    @18
    c1o
    @22
    c1o
    @2
    cvv
    df1o2
    @14
    eqeltri
    mapsnen
    vtoclg
    @3
    cA
    @5
    cA
    xpen
    syl2anc
    @1
    @6
    @7
    entr
    syl2anc
end

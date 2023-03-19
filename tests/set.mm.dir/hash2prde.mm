include "wcel.mm"
include "chash.mm"
include "cfv.mm"
include "c2.mm"
include "wceq.mm"
include "wa.mm"
include "cv.mm"
include "cpr.mm"
include "wex.mm"
include "wne.mm"
include "hash2pr.mm"
include "wi.mm"
include "weq.mm"
include "equid.mm"
include "csn.mm"
include "vex.mm"
include "preqsn.mm"
include "eqeq2.mm"
include "c1.mm"
include "fveq2.mm"
include "cvv.mm"
include "hashsng.mm"
include "ax-mp.mm"
include "syl6eq.mm"
include "eqeq1.mm"
include "1ne2.mm"
include "wn.mm"
include "df-ne.mm"
include "pm2.21.mm"
include "sylbi.mm"
include "eqcoms.mm"
include "syl6bi.mm"
include "adantl.mm"
include "syl5com.mm"
include "com13.mm"
include "imp.mm"
include "com12.mm"
include "sylbir.mm"
include "mpan2.mm"
include "ax-1.mm"
include "pm2.61ine.mm"
include "simpr.mm"
include "jca.mm"
include "ex.mm"
include "2eximdv.mm"
include "mpd.mm"

theorem hash2prde
  let cV: class V
  let cW: class W
  let va: setvar a
  let vb: setvar b

  disjoint V a
  disjoint V b
  disjoint a b
  disjoint W a
  disjoint W b
  assert |- ( ( V e. W /\ ( # ` V ) = 2 ) -> E. a E. b ( a =/= b /\ V = { a , b } ) )

  proof
    cV
    cW
    wcel
    #
    cV
    chash
    cfv
    #
    c2
    wceq
    #
    wa
    #
    cV
    va
    cv
    #
    vb
    cv
    #
    cpr
    #
    wceq
    #
    vb
    wex
    va
    wex
    @4
    @5
    wne
    #
    @7
    wa
    #
    vb
    wex
    va
    wex
    cV
    cW
    va
    vb
    hash2pr
    @3
    @7
    @9
    va
    vb
    @3
    @7
    @9
    @3
    @7
    wa
    #
    @8
    @7
    @10
    @8
    wi
    #
    @4
    @5
    va
    vb
    weq
    #
    vb
    vb
    weq
    #
    @11
    vb
    equid
    @12
    @13
    wa
    @6
    @5
    csn
    #
    wceq
    #
    @11
    @4
    @5
    @5
    va
    vex
    vb
    vex
    #
    @16
    preqsn
    @10
    @15
    @8
    @3
    @7
    @15
    @8
    wi
    @15
    @7
    @3
    @8
    @15
    @7
    cV
    @14
    wceq
    #
    @3
    @8
    wi
    @6
    @14
    cV
    eqeq2
    @17
    @1
    c1
    wceq
    #
    @3
    @8
    @17
    @1
    @14
    chash
    cfv
    #
    c1
    cV
    @14
    chash
    fveq2
    @5
    cvv
    wcel
    @19
    c1
    wceq
    @16
    @5
    cvv
    hashsng
    ax-mp
    syl6eq
    @2
    @18
    @8
    wi
    @0
    @2
    @18
    c2
    c1
    wceq
    @8
    @1
    c2
    c1
    eqeq1
    @8
    c1
    c2
    c1
    c2
    wne
    #
    c1
    c2
    wceq
    #
    @8
    wi
    #
    1ne2
    @20
    @21
    wn
    @22
    c1
    c2
    df-ne
    @21
    @8
    pm2.21
    sylbi
    ax-mp
    eqcoms
    syl6bi
    adantl
    syl5com
    syl6bi
    com13
    imp
    com12
    sylbir
    mpan2
    @8
    @10
    ax-1
    pm2.61ine
    @3
    @7
    simpr
    jca
    ex
    2eximdv
    mpd
end

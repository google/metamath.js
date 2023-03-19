include "wcel.mm"
include "chash.mm"
include "cfv.mm"
include "c1.mm"
include "wceq.mm"
include "cv.mm"
include "csn.mm"
include "wex.mm"
include "cfn.mm"
include "wi.mm"
include "wa.mm"
include "c1o.mm"
include "cen.mm"
include "wbr.mm"
include "id.mm"
include "hash1.mm"
include "syl6eqr.mm"
include "adantl.mm"
include "wb.mm"
include "com.mm"
include "1onn.mm"
include "nnfi.mm"
include "mp1i.mm"
include "hashen.mm"
include "sylan2.mm"
include "mpbid.mm"
include "en1.mm"
include "sylib.mm"
include "ex.mm"
include "a1d.mm"
include "wn.mm"
include "cpnf.mm"
include "hashinf.mm"
include "eqeq1.mm"
include "wne.mm"
include "cr.mm"
include "1re.mm"
include "renepnf.mm"
include "ax-mp.mm"
include "df-ne.mm"
include "pm2.21.mm"
include "sylbi.mm"
include "eqcoms.mm"
include "syl6bi.mm"
include "syl.mm"
include "expcom.mm"
include "pm2.61i.mm"
include "fveq2.mm"
include "cvv.mm"
include "vex.mm"
include "hashsng.mm"
include "syl6eq.mm"
include "exlimiv.mm"
include "impbid1.mm"

theorem hash1snb
  let cV: class V
  let cW: class W
  let va: setvar a

  disjoint V a
  assert |- ( V e. W -> ( ( # ` V ) = 1 <-> E. a V = { a } ) )

  proof
    cV
    cW
    wcel
    #
    cV
    chash
    cfv
    #
    c1
    wceq
    #
    cV
    va
    cv
    #
    csn
    #
    wceq
    #
    va
    wex
    #
    cV
    cfn
    wcel
    #
    @0
    @2
    @6
    wi
    #
    wi
    @7
    @8
    @0
    @7
    @2
    @6
    @7
    @2
    wa
    #
    cV
    c1o
    cen
    wbr
    #
    @6
    @9
    @1
    c1o
    chash
    cfv
    #
    wceq
    #
    @10
    @2
    @12
    @7
    @2
    @1
    c1
    @11
    @2
    id
    hash1
    syl6eqr
    adantl
    @2
    @7
    c1o
    cfn
    wcel
    #
    @12
    @10
    wb
    c1o
    com
    wcel
    @13
    @2
    1onn
    c1o
    nnfi
    mp1i
    cV
    c1o
    hashen
    sylan2
    mpbid
    va
    cV
    en1
    sylib
    ex
    a1d
    @0
    @7
    wn
    #
    @8
    @0
    @14
    wa
    @1
    cpnf
    wceq
    #
    @8
    cV
    cW
    hashinf
    @15
    @2
    cpnf
    c1
    wceq
    @6
    @1
    cpnf
    c1
    eqeq1
    @6
    c1
    cpnf
    c1
    cpnf
    wne
    #
    c1
    cpnf
    wceq
    #
    @6
    wi
    #
    c1
    cr
    wcel
    @16
    1re
    c1
    renepnf
    ax-mp
    @16
    @17
    wn
    @18
    c1
    cpnf
    df-ne
    @17
    @6
    pm2.21
    sylbi
    ax-mp
    eqcoms
    syl6bi
    syl
    expcom
    pm2.61i
    @5
    @2
    va
    @5
    @1
    @4
    chash
    cfv
    #
    c1
    cV
    @4
    chash
    fveq2
    @3
    cvv
    wcel
    @19
    c1
    wceq
    va
    vex
    @3
    cvv
    hashsng
    ax-mp
    syl6eq
    exlimiv
    impbid1
end

include "cword.mm"
include "wcel.mm"
include "cc0.mm"
include "cfv.mm"
include "chash.mm"
include "creps.mm"
include "co.mm"
include "wceq.mm"
include "cv.mm"
include "cfzo.mm"
include "wral.mm"
include "wb.mm"
include "wi.mm"
include "c0.mm"
include "fveq2.mm"
include "hash0.mm"
include "syl6eq.mm"
include "wa.mm"
include "cvv.mm"
include "fvex.mm"
include "repsw0.mm"
include "ax-mp.mm"
include "eqcomi.mm"
include "simpr.mm"
include "oveq2.mm"
include "adantr.mm"
include "3eqtr4a.mm"
include "ral0.mm"
include "fzo0.mm"
include "raleqdv.mm"
include "mpbiri.mm"
include "2thd.mm"
include "mpancom.mm"
include "a1d.mm"
include "wne.mm"
include "w3a.mm"
include "df-3an.mm"
include "a1i.mm"
include "cn0.mm"
include "fstwrdne.mm"
include "ancoms.mm"
include "lencl.mm"
include "adantl.mm"
include "repsdf2.mm"
include "syl2anc.mm"
include "eqidd.mm"
include "jca.mm"
include "biantrurd.mm"
include "3bitr4d.mm"
include "ex.mm"
include "pm2.61ine.mm"

theorem repswsymballbi
  let vi: setvar i
  let cV: class V
  let cW: class W

  disjoint W i
  assert |- ( W e. Word V -> ( W = ( ( W ` 0 ) repeatS ( # ` W ) ) <-> A. i e. ( 0 ..^ ( # ` W ) ) ( W ` i ) = ( W ` 0 ) ) )

  proof
    cW
    cV
    cword
    wcel
    #
    cW
    cc0
    cW
    cfv
    #
    cW
    chash
    cfv
    #
    creps
    co
    #
    wceq
    #
    vi
    cv
    cW
    cfv
    @1
    wceq
    #
    vi
    cc0
    @2
    cfzo
    co
    #
    wral
    #
    wb
    #
    wi
    cW
    c0
    cW
    c0
    wceq
    #
    @8
    @0
    @2
    cc0
    wceq
    #
    @9
    @8
    @9
    @2
    c0
    chash
    cfv
    cc0
    cW
    c0
    chash
    fveq2
    hash0
    syl6eq
    @10
    @9
    wa
    #
    @4
    @7
    @11
    c0
    @1
    cc0
    creps
    co
    #
    cW
    @3
    @12
    c0
    @1
    cvv
    wcel
    @12
    c0
    wceq
    cc0
    cW
    fvex
    @1
    cvv
    repsw0
    ax-mp
    eqcomi
    @10
    @9
    simpr
    @10
    @3
    @12
    wceq
    @9
    @2
    cc0
    @1
    creps
    oveq2
    adantr
    3eqtr4a
    @10
    @7
    @9
    @10
    @7
    @5
    vi
    c0
    wral
    @5
    vi
    ral0
    @10
    @5
    vi
    @6
    c0
    @10
    @6
    cc0
    cc0
    cfzo
    co
    c0
    @2
    cc0
    cc0
    cfzo
    oveq2
    cc0
    fzo0
    syl6eq
    raleqdv
    mpbiri
    adantr
    2thd
    mpancom
    a1d
    cW
    c0
    wne
    #
    @0
    @8
    @13
    @0
    wa
    #
    @0
    @2
    @2
    wceq
    #
    @7
    w3a
    #
    @0
    @15
    wa
    #
    @7
    wa
    #
    @4
    @7
    @16
    @18
    wb
    @14
    @0
    @15
    @7
    df-3an
    a1i
    @14
    @1
    cV
    wcel
    #
    @2
    cn0
    wcel
    #
    @4
    @16
    wb
    @0
    @13
    @19
    cV
    cW
    fstwrdne
    ancoms
    @0
    @20
    @13
    cV
    cW
    lencl
    adantl
    @1
    vi
    @2
    cV
    cW
    repsdf2
    syl2anc
    @14
    @17
    @7
    @14
    @0
    @15
    @13
    @0
    simpr
    @14
    @2
    eqidd
    jca
    biantrurd
    3bitr4d
    ex
    pm2.61ine
end

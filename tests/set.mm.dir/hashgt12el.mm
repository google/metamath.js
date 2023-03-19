include "c0.mm"
include "wceq.mm"
include "wcel.mm"
include "c1.mm"
include "chash.mm"
include "cfv.mm"
include "clt.mm"
include "wbr.mm"
include "wa.mm"
include "cv.mm"
include "wne.mm"
include "wrex.mm"
include "wi.mm"
include "cc0.mm"
include "hash0.mm"
include "fveq2.mm"
include "syl5eqr.mm"
include "breq2.mm"
include "biimpd.mm"
include "eqcoms.mm"
include "cle.mm"
include "0le1.mm"
include "wn.mm"
include "0re.mm"
include "1re.mm"
include "lenlti.mm"
include "pm2.21.mm"
include "sylbi.mm"
include "ax-mp.mm"
include "syl6com.mm"
include "adantl.mm"
include "com12.mm"
include "syl.mm"
include "df-ne.mm"
include "necom.mm"
include "bitr3i.mm"
include "weq.mm"
include "wral.mm"
include "ralnex.mm"
include "nne.mm"
include "equcom.mm"
include "bitri.mm"
include "ralbii.mm"
include "csn.mm"
include "wb.mm"
include "eqsn.mm"
include "bicomd.mm"
include "ralbidv.mm"
include "hashsnle1.mm"
include "syl6eqbr.mm"
include "a1i.mm"
include "reximdva0.mm"
include "r19.36v.mm"
include "sylbid.mm"
include "cxr.mm"
include "hashxrcl.mm"
include "adantr.mm"
include "rexri.mm"
include "xrlenlt.mm"
include "sylancl.mm"
include "sylibd.mm"
include "syl5bi.mm"
include "con4d.mm"
include "impancom.mm"
include "pm2.61i.mm"

theorem hashgt12el
  let cV: class V
  let cW: class W
  let va: setvar a
  let vb: setvar b

  disjoint W a
  disjoint V a
  disjoint V b
  disjoint a b
  assert |- ( ( V e. W /\ 1 < ( # ` V ) ) -> E. a e. V E. b e. V a =/= b )

  proof
    c0
    cV
    wceq
    #
    cV
    cW
    wcel
    #
    c1
    cV
    chash
    cfv
    #
    clt
    wbr
    #
    wa
    #
    va
    cv
    #
    vb
    cv
    #
    wne
    #
    vb
    cV
    wrex
    #
    va
    cV
    wrex
    #
    wi
    #
    @0
    cc0
    @2
    wceq
    #
    @10
    @0
    cc0
    c0
    chash
    cfv
    @2
    hash0
    c0
    cV
    chash
    fveq2
    syl5eqr
    @4
    @11
    @9
    @3
    @11
    @9
    wi
    @1
    @11
    @3
    c1
    cc0
    clt
    wbr
    #
    @9
    @3
    @12
    wi
    @2
    cc0
    @2
    cc0
    wceq
    @3
    @12
    @2
    cc0
    c1
    clt
    breq2
    biimpd
    eqcoms
    cc0
    c1
    cle
    wbr
    #
    @12
    @9
    wi
    #
    0le1
    @13
    @12
    wn
    @14
    cc0
    c1
    0re
    1re
    lenlti
    @12
    @9
    pm2.21
    sylbi
    ax-mp
    syl6com
    adantl
    com12
    syl
    @0
    wn
    #
    cV
    c0
    wne
    #
    @10
    @15
    c0
    cV
    wne
    @16
    c0
    cV
    df-ne
    c0
    cV
    necom
    bitr3i
    @4
    @16
    @9
    @1
    @16
    @3
    @9
    @1
    @16
    wa
    #
    @9
    @3
    @9
    wn
    #
    vb
    va
    weq
    #
    vb
    cV
    wral
    #
    va
    cV
    wral
    #
    @17
    @3
    wn
    #
    @18
    @8
    wn
    #
    va
    cV
    wral
    @21
    @8
    va
    cV
    ralnex
    @23
    @20
    va
    cV
    @23
    @7
    wn
    #
    vb
    cV
    wral
    @20
    @7
    vb
    cV
    ralnex
    @24
    @19
    vb
    cV
    @24
    va
    vb
    weq
    @19
    @5
    @6
    nne
    va
    vb
    equcom
    bitri
    ralbii
    bitr3i
    ralbii
    bitr3i
    @17
    @21
    @2
    c1
    cle
    wbr
    #
    @22
    @17
    @21
    cV
    @5
    csn
    #
    wceq
    #
    va
    cV
    wral
    #
    @25
    @17
    @20
    @27
    va
    cV
    @17
    @27
    @20
    @16
    @27
    @20
    wb
    @1
    vb
    cV
    @5
    eqsn
    adantl
    bicomd
    ralbidv
    @17
    @27
    @25
    wi
    #
    va
    cV
    wrex
    @28
    @25
    wi
    @1
    @29
    va
    cV
    @29
    @1
    @5
    cV
    wcel
    wa
    @27
    @2
    @26
    chash
    cfv
    c1
    cle
    cV
    @26
    chash
    fveq2
    @5
    hashsnle1
    syl6eqbr
    a1i
    reximdva0
    @27
    @25
    va
    cV
    r19.36v
    syl
    sylbid
    @17
    @2
    cxr
    wcel
    #
    c1
    cxr
    wcel
    @25
    @22
    wb
    @1
    @30
    @16
    cV
    cW
    hashxrcl
    adantr
    c1
    1re
    rexri
    @2
    c1
    xrlenlt
    sylancl
    sylibd
    syl5bi
    con4d
    impancom
    com12
    sylbi
    pm2.61i
end

include "c0.mm"
include "wceq.mm"
include "wcel.mm"
include "c1.mm"
include "chash.mm"
include "cfv.mm"
include "clt.mm"
include "wbr.mm"
include "w3a.mm"
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
include "3ad2ant2.mm"
include "syl5com.mm"
include "df-ne.mm"
include "necom.mm"
include "bitr3i.mm"
include "wa.mm"
include "wral.mm"
include "ralnex.mm"
include "nne.mm"
include "eqcom.mm"
include "bitri.mm"
include "ralbii.mm"
include "csn.mm"
include "wb.mm"
include "eqsn.mm"
include "bicomd.mm"
include "adantl.mm"
include "adantr.mm"
include "hashsnle1.mm"
include "breq1d.mm"
include "mpbiri.mm"
include "ex.mm"
include "sylbid.mm"
include "cxr.mm"
include "hashxrcl.mm"
include "rexri.mm"
include "xrlenlt.mm"
include "sylancl.mm"
include "sylibd.mm"
include "syl5bi.mm"
include "con4d.mm"
include "exp31.mm"
include "com24.mm"
include "3imp.mm"
include "com12.mm"
include "pm2.61i.mm"

theorem hashgt12el2
  let cA: class A
  let cV: class V
  let cW: class W
  let vb: setvar b
  let va: setvar a

  disjoint V b
  disjoint A b
  disjoint W a
  disjoint V a
  disjoint a b
  assert |- ( ( V e. W /\ 1 < ( # ` V ) /\ A e. V ) -> E. b e. V A =/= b )

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
    cA
    cV
    wcel
    #
    w3a
    #
    cA
    vb
    cv
    #
    wne
    #
    vb
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
    @5
    @8
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
    @3
    @1
    @10
    @8
    wi
    @4
    @10
    @3
    c1
    cc0
    clt
    wbr
    #
    @8
    @3
    @11
    wi
    @2
    cc0
    @2
    cc0
    wceq
    @3
    @11
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
    @11
    @8
    wi
    #
    0le1
    @12
    @11
    wn
    @13
    cc0
    c1
    0re
    1re
    lenlti
    @11
    @8
    pm2.21
    sylbi
    ax-mp
    syl6com
    3ad2ant2
    syl5com
    @0
    wn
    #
    cV
    c0
    wne
    #
    @9
    @14
    c0
    cV
    wne
    @15
    c0
    cV
    df-ne
    c0
    cV
    necom
    bitr3i
    @5
    @15
    @8
    @1
    @3
    @4
    @15
    @8
    wi
    @1
    @15
    @4
    @3
    @8
    @1
    @15
    @4
    @3
    @8
    wi
    @1
    @15
    wa
    #
    @4
    wa
    #
    @8
    @3
    @8
    wn
    #
    @6
    cA
    wceq
    #
    vb
    cV
    wral
    #
    @17
    @3
    wn
    #
    @18
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
    @22
    @19
    vb
    cV
    @22
    cA
    @6
    wceq
    @19
    cA
    @6
    nne
    cA
    @6
    eqcom
    bitri
    ralbii
    bitr3i
    @17
    @20
    @2
    c1
    cle
    wbr
    #
    @21
    @17
    @20
    cV
    cA
    csn
    #
    wceq
    #
    @23
    @16
    @20
    @25
    wb
    #
    @4
    @15
    @26
    @1
    @15
    @25
    @20
    vb
    cV
    cA
    eqsn
    bicomd
    adantl
    adantr
    @17
    @25
    @23
    @17
    @25
    wa
    @23
    @24
    chash
    cfv
    #
    c1
    cle
    wbr
    #
    cA
    hashsnle1
    @25
    @23
    @28
    wb
    @17
    @25
    @2
    @27
    c1
    cle
    cV
    @24
    chash
    fveq2
    breq1d
    adantl
    mpbiri
    ex
    sylbid
    @17
    @2
    cxr
    wcel
    #
    c1
    cxr
    wcel
    @23
    @21
    wb
    @16
    @29
    @4
    @1
    @29
    @15
    cV
    cW
    hashxrcl
    adantr
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
    exp31
    com24
    3imp
    com12
    sylbi
    pm2.61i
end

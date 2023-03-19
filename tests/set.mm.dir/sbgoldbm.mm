include "c4.mm"
include "cv.mm"
include "clt.mm"
include "wbr.mm"
include "cgbe.mm"
include "wcel.mm"
include "wi.mm"
include "ceven.mm"
include "wral.mm"
include "caddc.mm"
include "co.mm"
include "wceq.mm"
include "cprime.mm"
include "wrex.mm"
include "c6.mm"
include "cuz.mm"
include "cfv.mm"
include "breq2.mm"
include "eleq1w.mm"
include "imbi12d.mm"
include "cbvralv.mm"
include "cz.mm"
include "cle.mm"
include "w3a.mm"
include "eluz2.mm"
include "codd.mm"
include "wo.mm"
include "zeoALTV.mm"
include "sgoldbeven3prm.mm"
include "expdcom.mm"
include "c5.mm"
include "cgbow.mm"
include "sbgoldbwt.mm"
include "wa.mm"
include "rspa.mm"
include "c1.mm"
include "df-6.mm"
include "breq1i.mm"
include "wb.mm"
include "5nn.mm"
include "nnzi.mm"
include "oddz.mm"
include "zltp1le.mm"
include "sylancr.mm"
include "biimprd.mm"
include "syl5bi.mm"
include "imp.mm"
include "isgbow.mm"
include "simprbi.mm"
include "a1i.mm"
include "embantd.mm"
include "ex.mm"
include "com23.mm"
include "adantl.mm"
include "mpd.mm"
include "syl.mm"
include "com13.mm"
include "jaoi.mm"
include "3adant1.mm"
include "sylbi.mm"
include "impcom.mm"
include "ralrimiva.mm"

theorem sbgoldbm
  let vn: setvar n
  let vr: setvar r
  let vq: setvar q
  let vp: setvar p
  let vm: setvar m
  let vk: setvar k
  let vx: setvar x

  disjoint n p
  disjoint n q
  disjoint n r
  disjoint p q
  disjoint p r
  disjoint q r
  disjoint m n
  disjoint m p
  disjoint m q
  disjoint m r
  disjoint k x
  assert |- ( A. n e. Even ( 4 < n -> n e. GoldbachEven ) -> A. n e. ( ZZ>= ` 6 ) E. p e. Prime E. q e. Prime E. r e. Prime n = ( ( p + q ) + r ) )

  proof
    c4
    vn
    cv
    #
    clt
    wbr
    #
    @0
    cgbe
    wcel
    #
    wi
    #
    vn
    ceven
    wral
    c4
    vm
    cv
    #
    clt
    wbr
    #
    @4
    cgbe
    wcel
    #
    wi
    #
    vm
    ceven
    wral
    #
    @0
    vp
    cv
    vq
    cv
    caddc
    co
    vr
    cv
    caddc
    co
    wceq
    vr
    cprime
    wrex
    vq
    cprime
    wrex
    vp
    cprime
    wrex
    #
    vn
    c6
    cuz
    cfv
    #
    wral
    @3
    @7
    vn
    vm
    ceven
    @0
    @4
    wceq
    @1
    @5
    @2
    @6
    @0
    @4
    c4
    clt
    breq2
    vn
    vm
    cgbe
    eleq1w
    imbi12d
    cbvralv
    @8
    @9
    vn
    @10
    @0
    @10
    wcel
    #
    @8
    @9
    @11
    c6
    cz
    wcel
    #
    @0
    cz
    wcel
    #
    c6
    @0
    cle
    wbr
    #
    w3a
    @8
    @9
    wi
    #
    c6
    @0
    eluz2
    @13
    @14
    @15
    @12
    @13
    @14
    @15
    @13
    @0
    ceven
    wcel
    #
    @0
    codd
    wcel
    #
    wo
    @14
    @15
    wi
    #
    @0
    zeoALTV
    @16
    @18
    @17
    @8
    @16
    @14
    @9
    vm
    @0
    vr
    vq
    vp
    sgoldbeven3prm
    expdcom
    @8
    @14
    @17
    @9
    @8
    c5
    @0
    clt
    wbr
    #
    @0
    cgbow
    wcel
    #
    wi
    #
    vn
    codd
    wral
    #
    @14
    @17
    @9
    wi
    wi
    vn
    vm
    sbgoldbwt
    @22
    @17
    @14
    @9
    @22
    @17
    @14
    @9
    wi
    #
    @22
    @17
    wa
    @21
    @23
    @21
    vn
    codd
    rspa
    @17
    @21
    @23
    wi
    @22
    @17
    @14
    @21
    @9
    @17
    @14
    @21
    @9
    wi
    @17
    @14
    wa
    #
    @19
    @20
    @9
    @17
    @14
    @19
    @14
    c5
    c1
    caddc
    co
    #
    @0
    cle
    wbr
    #
    @17
    @19
    c6
    @25
    @0
    cle
    df-6
    breq1i
    @17
    @19
    @26
    @17
    c5
    cz
    wcel
    @13
    @19
    @26
    wb
    c5
    5nn
    nnzi
    @0
    oddz
    c5
    @0
    zltp1le
    sylancr
    biimprd
    syl5bi
    imp
    @20
    @9
    wi
    @24
    @20
    @17
    @9
    @0
    vr
    vq
    vp
    isgbow
    simprbi
    a1i
    embantd
    ex
    com23
    adantl
    mpd
    ex
    com23
    syl
    com13
    jaoi
    syl
    imp
    3adant1
    sylbi
    impcom
    ralrimiva
    sylbi
end

include "crusgr.mm"
include "wbr.mm"
include "wcel.mm"
include "wa.mm"
include "cc0.mm"
include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "c1.mm"
include "cwwlksn.mm"
include "co.mm"
include "crab.mm"
include "chash.mm"
include "c2.mm"
include "cpr.mm"
include "cedg.mm"
include "w3a.mm"
include "cword.mm"
include "c0.mm"
include "wne.mm"
include "caddc.mm"
include "cmin.mm"
include "cfzo.mm"
include "wral.mm"
include "wb.mm"
include "cwwlks.mm"
include "cn0.mm"
include "1nn0.mm"
include "iswwlksn.mm"
include "ax-mp.mm"
include "eqid.mm"
include "iswwlks.mm"
include "anbi1i.mm"
include "bitri.mm"
include "a1i.mm"
include "anbi1d.mm"
include "1p1e2.mm"
include "eqeq2i.mm"
include "anbi2d.mm"
include "3anass.mm"
include "wn.mm"
include "fveq2.mm"
include "hash0.mm"
include "syl6eq.mm"
include "2ne0.mm"
include "nesymi.mm"
include "eqeq1.mm"
include "mtbiri.mm"
include "syl.mm"
include "necon2ai.mm"
include "adantl.mm"
include "biantrurd.mm"
include "oveq1.mm"
include "2m1e1.mm"
include "oveq2d.mm"
include "raleqdv.mm"
include "csn.mm"
include "fzo01.mm"
include "raleqi.mm"
include "c0ex.mm"
include "0p1e1.mm"
include "fveq2d.mm"
include "preq12d.mm"
include "eleq1d.mm"
include "ralsn.mm"
include "syl6bb.mm"
include "3bitr2d.mm"
include "ex.mm"
include "pm5.32rd.mm"
include "bitrd.mm"
include "anass.mm"
include "ancom.mm"
include "df-3an.mm"
include "bitr4i.mm"
include "anbi2i.mm"
include "3bitrd.mm"
include "rabbidva2.mm"
include "rusgrnumwrdl2.mm"
include "eqtrd.mm"

theorem rusgrnumwwlkl1
  let vw: setvar w
  let cP: class P
  let cG: class G
  let cK: class K
  let cV: class V
  let vi: setvar i
  assume rusgrnumwwlkl1.v: |- V = ( Vtx ` G )

  disjoint G w
  disjoint K w
  disjoint P w
  disjoint V w
  disjoint G i
  disjoint i w
  assert |- ( ( G RegUSGraph K /\ P e. V ) -> ( # ` { w e. ( 1 WWalksN G ) | ( w ` 0 ) = P } ) = K )

  proof
    cG
    cK
    crusgr
    wbr
    cP
    cV
    wcel
    wa
    #
    cc0
    vw
    cv
    #
    cfv
    #
    cP
    wceq
    #
    vw
    c1
    cG
    cwwlksn
    co
    #
    crab
    #
    chash
    cfv
    @1
    chash
    cfv
    #
    c2
    wceq
    #
    @3
    @2
    c1
    @1
    cfv
    #
    cpr
    #
    cG
    cedg
    cfv
    #
    wcel
    #
    w3a
    #
    vw
    cV
    cword
    #
    crab
    #
    chash
    cfv
    cK
    @0
    @5
    @14
    chash
    @0
    @3
    @12
    vw
    @4
    @13
    @0
    @1
    @4
    wcel
    #
    @3
    wa
    @1
    c0
    wne
    #
    @1
    @13
    wcel
    #
    vi
    cv
    #
    @1
    cfv
    #
    @18
    c1
    caddc
    co
    #
    @1
    cfv
    #
    cpr
    #
    @10
    wcel
    #
    vi
    cc0
    @6
    c1
    cmin
    co
    #
    cfzo
    co
    #
    wral
    #
    w3a
    #
    @6
    c1
    c1
    caddc
    co
    #
    wceq
    #
    wa
    #
    @3
    wa
    #
    @17
    @11
    wa
    #
    @7
    @3
    wa
    #
    wa
    #
    @17
    @12
    wa
    #
    @0
    @15
    @30
    @3
    @15
    @30
    wb
    @0
    @15
    @1
    cG
    cwwlks
    cfv
    wcel
    #
    @29
    wa
    #
    @30
    c1
    cn0
    wcel
    @15
    @37
    wb
    1nn0
    cG
    c1
    @1
    iswwlksn
    ax-mp
    @36
    @27
    @29
    vi
    @10
    cG
    cV
    @1
    rusgrnumwwlkl1.v
    @10
    eqid
    iswwlks
    anbi1i
    bitri
    a1i
    anbi1d
    @0
    @31
    @32
    @7
    wa
    #
    @3
    wa
    @34
    @0
    @30
    @38
    @3
    @0
    @30
    @27
    @7
    wa
    @38
    @0
    @29
    @7
    @27
    @29
    @7
    wb
    @0
    @28
    c2
    @6
    1p1e2
    eqeq2i
    a1i
    anbi2d
    @0
    @7
    @27
    @32
    @0
    @7
    @27
    @32
    wb
    @0
    @7
    wa
    #
    @27
    @16
    @17
    @26
    wa
    #
    wa
    #
    @40
    @32
    @27
    @41
    wb
    @39
    @16
    @17
    @26
    3anass
    a1i
    @39
    @16
    @40
    @7
    @16
    @0
    @7
    @1
    c0
    @1
    c0
    wceq
    #
    @6
    cc0
    wceq
    #
    @7
    wn
    @42
    @6
    c0
    chash
    cfv
    cc0
    @1
    c0
    chash
    fveq2
    hash0
    syl6eq
    @43
    @7
    cc0
    c2
    wceq
    c2
    cc0
    2ne0
    nesymi
    @6
    cc0
    c2
    eqeq1
    mtbiri
    syl
    necon2ai
    adantl
    biantrurd
    @39
    @26
    @11
    @17
    @39
    @26
    @23
    vi
    cc0
    c1
    cfzo
    co
    #
    wral
    #
    @11
    @39
    @23
    vi
    @25
    @44
    @7
    @25
    @44
    wceq
    @0
    @7
    @24
    c1
    cc0
    cfzo
    @7
    @24
    c2
    c1
    cmin
    co
    c1
    @6
    c2
    c1
    cmin
    oveq1
    2m1e1
    syl6eq
    oveq2d
    adantl
    raleqdv
    @45
    @23
    vi
    cc0
    csn
    #
    wral
    @11
    @23
    vi
    @44
    @46
    fzo01
    raleqi
    @23
    @11
    vi
    cc0
    c0ex
    @18
    cc0
    wceq
    #
    @22
    @9
    @10
    @47
    @19
    @2
    @21
    @8
    @18
    cc0
    @1
    fveq2
    @47
    @20
    c1
    @1
    @47
    @20
    cc0
    c1
    caddc
    co
    c1
    @18
    cc0
    c1
    caddc
    oveq1
    0p1e1
    syl6eq
    fveq2d
    preq12d
    eleq1d
    ralsn
    bitri
    syl6bb
    anbi2d
    3bitr2d
    ex
    pm5.32rd
    bitrd
    anbi1d
    @32
    @7
    @3
    anass
    syl6bb
    @34
    @35
    wb
    @0
    @34
    @17
    @11
    @33
    wa
    #
    wa
    @35
    @17
    @11
    @33
    anass
    @48
    @12
    @17
    @48
    @33
    @11
    wa
    @12
    @11
    @33
    ancom
    @7
    @3
    @11
    df-3an
    bitr4i
    anbi2i
    bitri
    a1i
    3bitrd
    rabbidva2
    fveq2d
    vw
    cP
    cG
    cK
    cV
    rusgrnumwwlkl1.v
    rusgrnumwrdl2
    eqtrd
end

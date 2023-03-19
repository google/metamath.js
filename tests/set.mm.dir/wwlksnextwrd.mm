include "cwwlksn.mm"
include "co.mm"
include "wcel.mm"
include "cv.mm"
include "chash.mm"
include "cfv.mm"
include "c2.mm"
include "caddc.mm"
include "wceq.mm"
include "cc0.mm"
include "c1.mm"
include "cop.mm"
include "csubstr.mm"
include "clsw.mm"
include "cpr.mm"
include "w3a.mm"
include "cword.mm"
include "crab.mm"
include "wa.mm"
include "3anass.mm"
include "bianass.mm"
include "wb.mm"
include "wi.mm"
include "cvv.mm"
include "cn0.mm"
include "wwlknbp.mm"
include "cs1.mm"
include "cconcat.mm"
include "simpl.mm"
include "c0.mm"
include "wne.mm"
include "clt.mm"
include "wbr.mm"
include "nn0re.mm"
include "cr.mm"
include "2re.mm"
include "a1i.mm"
include "nn0ge0.mm"
include "2pos.mm"
include "addgegt0d.mm"
include "adantr.mm"
include "breq2.mm"
include "ad2antll.mm"
include "mpbird.mm"
include "hashgt0n0.mm"
include "syl2an2.mm"
include "lswcl.mm"
include "adantrr.mm"
include "swrdcl.mm"
include "eleq1.mm"
include "syl5ibr.mm"
include "eqcoms.mm"
include "com12.mm"
include "imp.mm"
include "adantl.mm"
include "oveq1.mm"
include "cmin.mm"
include "nn0cn.mm"
include "2cnd.mm"
include "1cnd.mm"
include "addsubassd.mm"
include "2m1e1.mm"
include "oveq2d.mm"
include "eqtrd.mm"
include "sylan9eqr.mm"
include "opeq2d.mm"
include "oveq1d.mm"
include "swrdccatwrd.mm"
include "eqtr3d.mm"
include "eqtr2d.mm"
include "simprrr.mm"
include "wwlksnextbi.mm"
include "syl23anc.mm"
include "exbiri.mm"
include "com23.mm"
include "3ad2ant2.mm"
include "mpcom.mm"
include "expcomd.mm"
include "cfzo.mm"
include "wral.mm"
include "wwlknp.mm"
include "addassd.mm"
include "1p1e2.mm"
include "eqeq2d.mm"
include "biimpd.mm"
include "jctild.mm"
include "3adant3.mm"
include "syl.mm"
include "3adant1.mm"
include "impbid.mm"
include "ex.mm"
include "pm5.32rd.mm"
include "syl5bb.mm"
include "rabbidva2.mm"
include "syl5eq.mm"

theorem wwlksnextwrd
  let vw: setvar w
  let cD: class D
  let cE: class E
  let cG: class G
  let cN: class N
  let cV: class V
  let cW: class W
  let vi: setvar i
  assume wwlksnextbij0.v: |- V = ( Vtx ` G )
  assume wwlksnextbij0.e: |- E = ( Edg ` G )
  assume wwlksnextbij0.d: |- D = { w e. Word V | ( ( # ` w ) = ( N + 2 ) /\ ( w substr <. 0 , ( N + 1 ) >. ) = W /\ { ( lastS ` W ) , ( lastS ` w ) } e. E ) }

  disjoint G w
  disjoint N w
  disjoint W w
  disjoint G i
  disjoint i w
  disjoint N i
  assert |- ( W e. ( N WWalksN G ) -> D = { w e. ( ( N + 1 ) WWalksN G ) | ( ( w substr <. 0 , ( N + 1 ) >. ) = W /\ { ( lastS ` W ) , ( lastS ` w ) } e. E ) } )

  proof
    cW
    cN
    cG
    cwwlksn
    co
    wcel
    #
    cD
    vw
    cv
    #
    chash
    cfv
    #
    cN
    c2
    caddc
    co
    #
    wceq
    #
    @1
    cc0
    cN
    c1
    caddc
    co
    #
    cop
    #
    csubstr
    co
    #
    cW
    wceq
    #
    cW
    clsw
    cfv
    @1
    clsw
    cfv
    #
    cpr
    cE
    wcel
    #
    w3a
    #
    vw
    cV
    cword
    #
    crab
    @8
    @10
    wa
    #
    vw
    @5
    cG
    cwwlksn
    co
    #
    crab
    wwlksnextbij0.d
    @0
    @11
    @13
    vw
    @12
    @14
    @1
    @12
    wcel
    #
    @11
    wa
    @15
    @4
    wa
    #
    @13
    wa
    #
    @0
    @1
    @14
    wcel
    #
    @13
    wa
    @11
    @4
    @13
    @15
    @4
    @8
    @10
    3anass
    bianass
    @0
    @13
    @16
    @18
    @0
    @13
    @16
    @18
    wb
    @0
    @13
    wa
    @16
    @18
    @0
    @13
    @16
    @18
    wi
    @0
    @16
    @13
    @18
    cG
    cvv
    wcel
    #
    cN
    cn0
    wcel
    #
    cW
    @12
    wcel
    #
    w3a
    #
    @0
    @17
    @18
    wi
    #
    cG
    cN
    cV
    cW
    wwlksnextbij0.v
    wwlknbp
    #
    @20
    @19
    @0
    @23
    wi
    @21
    @20
    @17
    @0
    @18
    @20
    @17
    @18
    @0
    @20
    @17
    wa
    #
    @20
    @9
    cV
    wcel
    #
    @21
    @1
    cW
    @9
    cs1
    #
    cconcat
    co
    #
    wceq
    @10
    @18
    @0
    wb
    @20
    @17
    simpl
    @20
    @16
    @26
    @13
    @16
    @15
    @20
    @1
    c0
    wne
    #
    @26
    @15
    @4
    simpl
    #
    @16
    @15
    @20
    cc0
    @2
    clt
    wbr
    #
    @29
    @30
    @20
    @16
    wa
    #
    @31
    cc0
    @3
    clt
    wbr
    #
    @20
    @33
    @16
    @20
    cN
    c2
    cN
    nn0re
    c2
    cr
    wcel
    @20
    2re
    a1i
    cN
    nn0ge0
    cc0
    c2
    clt
    wbr
    @20
    2pos
    a1i
    addgegt0d
    adantr
    @4
    @31
    @33
    wb
    @20
    @15
    @2
    @3
    cc0
    clt
    breq2
    ad2antll
    mpbird
    @1
    @12
    hashgt0n0
    syl2an2
    #
    cV
    @1
    lswcl
    syl2an2
    adantrr
    @17
    @21
    @20
    @16
    @13
    @21
    @15
    @13
    @21
    wi
    @4
    @13
    @15
    @21
    @8
    @15
    @21
    wi
    #
    @10
    @35
    cW
    @7
    @15
    @21
    cW
    @7
    wceq
    @7
    @12
    wcel
    cV
    @1
    cc0
    @5
    swrdcl
    cW
    @7
    @12
    eleq1
    syl5ibr
    eqcoms
    adantr
    com12
    adantr
    imp
    adantl
    @25
    @28
    @7
    @27
    cconcat
    co
    #
    @1
    @13
    @28
    @36
    wceq
    #
    @20
    @16
    @8
    @37
    @10
    @37
    cW
    @7
    cW
    @7
    @27
    cconcat
    oveq1
    eqcoms
    adantr
    ad2antll
    @20
    @16
    @36
    @1
    wceq
    @13
    @32
    @1
    cc0
    @2
    c1
    cmin
    co
    #
    cop
    #
    csubstr
    co
    #
    @27
    cconcat
    co
    #
    @36
    @1
    @32
    @40
    @7
    @27
    cconcat
    @32
    @39
    @6
    @1
    csubstr
    @32
    @38
    @5
    cc0
    @16
    @20
    @38
    @3
    c1
    cmin
    co
    #
    @5
    @4
    @38
    @42
    wceq
    @15
    @2
    @3
    c1
    cmin
    oveq1
    adantl
    @20
    @42
    cN
    c2
    c1
    cmin
    co
    #
    caddc
    co
    @5
    @20
    cN
    c2
    c1
    cN
    nn0cn
    #
    @20
    2cnd
    @20
    1cnd
    #
    addsubassd
    @20
    @43
    c1
    cN
    caddc
    @43
    c1
    wceq
    @20
    2m1e1
    a1i
    oveq2d
    eqtrd
    sylan9eqr
    opeq2d
    oveq2d
    oveq1d
    @16
    @15
    @20
    @29
    @41
    @1
    wceq
    @30
    @34
    cV
    @1
    swrdccatwrd
    syl2an2
    eqtr3d
    adantrr
    eqtr2d
    @20
    @16
    @8
    @10
    simprrr
    @9
    cW
    cE
    cG
    cN
    cV
    @1
    wwlksnextbij0.v
    wwlksnextbij0.e
    wwlksnextbi
    syl23anc
    exbiri
    com23
    3ad2ant2
    mpcom
    expcomd
    imp
    @0
    @18
    @16
    wi
    #
    @13
    @0
    @22
    @46
    @24
    @20
    @21
    @46
    @19
    @18
    @20
    @21
    wa
    #
    @16
    @18
    @15
    @2
    @5
    c1
    caddc
    co
    #
    wceq
    #
    vi
    cv
    #
    @1
    cfv
    @50
    c1
    caddc
    co
    @1
    cfv
    cpr
    cE
    wcel
    vi
    cc0
    @5
    cfzo
    co
    wral
    #
    w3a
    @47
    @16
    wi
    #
    vi
    cE
    cG
    @5
    cV
    @1
    wwlksnextbij0.v
    wwlksnextbij0.e
    wwlknp
    @15
    @49
    @52
    @51
    @15
    @49
    wa
    @47
    @4
    @15
    @49
    @47
    @4
    wi
    @15
    @47
    @49
    @4
    @20
    @49
    @4
    wi
    @21
    @20
    @49
    @4
    @20
    @48
    @3
    @2
    @20
    @48
    cN
    c1
    c1
    caddc
    co
    #
    caddc
    co
    @3
    @20
    cN
    c1
    c1
    @44
    @45
    @45
    addassd
    @20
    @53
    c2
    cN
    caddc
    @53
    c2
    wceq
    @20
    1p1e2
    a1i
    oveq2d
    eqtrd
    eqeq2d
    biimpd
    adantr
    com12
    adantl
    @15
    @49
    simpl
    jctild
    3adant3
    syl
    com12
    3adant1
    syl
    adantr
    impbid
    ex
    pm5.32rd
    syl5bb
    rabbidva2
    syl5eq
end

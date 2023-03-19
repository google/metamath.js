include "cn0.mm"
include "wcel.mm"
include "wa.mm"
include "cword.mm"
include "cs1.mm"
include "cconcat.mm"
include "co.mm"
include "wceq.mm"
include "clsw.mm"
include "cfv.mm"
include "cpr.mm"
include "w3a.mm"
include "c1.mm"
include "caddc.mm"
include "cwwlksn.mm"
include "chash.mm"
include "cv.mm"
include "cc0.mm"
include "cfzo.mm"
include "wral.mm"
include "wi.mm"
include "wwlknp.mm"
include "cop.mm"
include "csubstr.mm"
include "wwlksnred.mm"
include "ad2antrr.mm"
include "wb.mm"
include "fveq2.mm"
include "eqeq1d.mm"
include "3ad2ant2.mm"
include "adantl.mm"
include "s1cl.mm"
include "anim2i.mm"
include "ancoms.mm"
include "ccatlen.mm"
include "syl.mm"
include "s1len.mm"
include "a1i.mm"
include "oveq2d.mm"
include "cc.mm"
include "lencl.mm"
include "nn0cnd.mm"
include "peano2nn0.mm"
include "1cnd.mm"
include "addcan2d.mm"
include "3bitrd.mm"
include "opeq2.mm"
include "eqcoms.mm"
include "swrdccat1.mm"
include "sylan9eqr.mm"
include "ex.mm"
include "sylbid.mm"
include "3ad2antr1.mm"
include "imp.mm"
include "oveq1.mm"
include "ad2antlr.mm"
include "mpbird.mm"
include "eleq1d.mm"
include "biimpd.mm"
include "com23.mm"
include "syld.mm"
include "com13.mm"
include "mpcom.mm"
include "com12.mm"
include "wwlksnext.mm"
include "eleq1.mm"
include "syl5ibrcom.mm"
include "3exp.mm"
include "com14.mm"
include "3adant1.mm"
include "impbid.mm"

theorem wwlksnextbi
  let cS: class S
  let cT: class T
  let cE: class E
  let cG: class G
  let cN: class N
  let cV: class V
  let cW: class W
  let vi: setvar i
  assume wwlksnext.v: |- V = ( Vtx ` G )
  assume wwlksnext.e: |- E = ( Edg ` G )


  assert |- ( ( ( N e. NN0 /\ S e. V ) /\ ( T e. Word V /\ W = ( T ++ <" S "> ) /\ { ( lastS ` T ) , S } e. E ) ) -> ( W e. ( ( N + 1 ) WWalksN G ) <-> T e. ( N WWalksN G ) ) )

  proof
    cN
    cn0
    wcel
    #
    cS
    cV
    wcel
    #
    wa
    #
    cT
    cV
    cword
    #
    wcel
    #
    cW
    cT
    cS
    cs1
    #
    cconcat
    co
    #
    wceq
    #
    cT
    clsw
    cfv
    cS
    cpr
    cE
    wcel
    #
    w3a
    #
    wa
    #
    cW
    cN
    c1
    caddc
    co
    #
    cG
    cwwlksn
    co
    #
    wcel
    #
    cT
    cN
    cG
    cwwlksn
    co
    #
    wcel
    #
    @13
    @10
    @15
    cW
    @3
    wcel
    #
    cW
    chash
    cfv
    #
    @11
    c1
    caddc
    co
    #
    wceq
    #
    vi
    cv
    #
    cW
    cfv
    @20
    c1
    caddc
    co
    cW
    cfv
    cpr
    cE
    wcel
    vi
    cc0
    @11
    cfzo
    co
    wral
    #
    w3a
    @13
    @10
    @15
    wi
    #
    vi
    cE
    cG
    @11
    cV
    cW
    wwlksnext.v
    wwlksnext.e
    wwlknp
    @19
    @16
    @13
    @22
    wi
    @21
    @10
    @13
    @19
    @15
    @10
    @13
    cW
    cc0
    @11
    cop
    #
    csubstr
    co
    #
    @14
    wcel
    #
    @19
    @15
    wi
    @0
    @13
    @25
    wi
    @1
    @9
    cG
    cN
    cW
    wwlksnred
    ad2antrr
    @10
    @19
    @25
    @15
    @10
    @19
    @25
    @15
    wi
    @10
    @19
    wa
    #
    @25
    @15
    @26
    @24
    cT
    @14
    @26
    @24
    cT
    wceq
    #
    @6
    @23
    csubstr
    co
    #
    cT
    wceq
    #
    @10
    @19
    @29
    @10
    @19
    @6
    chash
    cfv
    #
    @18
    wceq
    #
    @29
    @9
    @19
    @31
    wb
    #
    @2
    @7
    @4
    @32
    @8
    @7
    @17
    @30
    @18
    cW
    @6
    chash
    fveq2
    eqeq1d
    3ad2ant2
    adantl
    @2
    @7
    @4
    @31
    @29
    wi
    @8
    @2
    @4
    wa
    #
    @31
    cT
    chash
    cfv
    #
    @11
    wceq
    #
    @29
    @33
    @31
    @34
    @5
    chash
    cfv
    #
    caddc
    co
    #
    @18
    wceq
    @34
    c1
    caddc
    co
    #
    @18
    wceq
    @35
    @33
    @30
    @37
    @18
    @33
    @4
    @5
    @3
    wcel
    #
    wa
    #
    @30
    @37
    wceq
    @4
    @2
    @40
    @2
    @39
    @4
    @1
    @39
    @0
    cS
    cV
    s1cl
    adantl
    anim2i
    ancoms
    #
    cV
    cT
    @5
    ccatlen
    syl
    eqeq1d
    @33
    @37
    @38
    @18
    @33
    @36
    c1
    @34
    caddc
    @36
    c1
    wceq
    @33
    cS
    s1len
    a1i
    oveq2d
    eqeq1d
    @33
    @34
    @11
    c1
    @4
    @34
    cc
    wcel
    @2
    @4
    @34
    cV
    cT
    lencl
    nn0cnd
    adantl
    @0
    @11
    cc
    wcel
    @1
    @4
    @0
    @11
    cN
    peano2nn0
    nn0cnd
    ad2antrr
    @33
    1cnd
    addcan2d
    3bitrd
    @33
    @35
    @29
    @35
    @33
    @28
    @6
    cc0
    @34
    cop
    #
    csubstr
    co
    #
    cT
    @35
    @23
    @42
    @6
    csubstr
    @23
    @42
    wceq
    @11
    @34
    @11
    @34
    cc0
    opeq2
    eqcoms
    oveq2d
    @33
    @40
    @43
    cT
    wceq
    @41
    cV
    cT
    @5
    swrdccat1
    syl
    sylan9eqr
    ex
    sylbid
    3ad2antr1
    sylbid
    imp
    @9
    @27
    @29
    wb
    #
    @2
    @19
    @7
    @4
    @44
    @8
    @7
    @24
    @28
    cT
    cW
    @6
    @23
    csubstr
    oveq1
    eqeq1d
    3ad2ant2
    ad2antlr
    mpbird
    eleq1d
    biimpd
    ex
    com23
    syld
    com13
    3ad2ant2
    mpcom
    com12
    @2
    @9
    @15
    @13
    wi
    #
    @1
    @9
    @45
    wi
    @0
    @9
    @1
    @45
    @7
    @8
    @1
    @45
    wi
    #
    @4
    @7
    @8
    @46
    @15
    @8
    @1
    @7
    @13
    @15
    @1
    @8
    @7
    @13
    wi
    #
    @15
    @1
    @8
    @47
    @15
    @1
    @8
    w3a
    @13
    @7
    @6
    @12
    wcel
    cS
    cT
    cE
    cG
    cN
    cV
    wwlksnext.v
    wwlksnext.e
    wwlksnext
    cW
    @6
    @12
    eleq1
    syl5ibrcom
    3exp
    com23
    com14
    imp
    3adant1
    com12
    adantl
    imp
    impbid
end

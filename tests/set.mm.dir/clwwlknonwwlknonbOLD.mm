include "cword.mm"
include "wcel.mm"
include "cn.mm"
include "w3a.mm"
include "cs1.mm"
include "cconcat.mm"
include "co.mm"
include "cwwlksn.mm"
include "cc0.mm"
include "cfv.mm"
include "wceq.mm"
include "cclwwlkn.mm"
include "wa.mm"
include "cwwlksnon.mm"
include "cclwwlknon.mm"
include "s1eq.mm"
include "oveq2d.mm"
include "eleq1d.mm"
include "biimpac.mm"
include "adantl.mm"
include "chash.mm"
include "wi.mm"
include "cn0.mm"
include "nnnn0.mm"
include "anim2i.mm"
include "3adant2.mm"
include "wwlksnprcl.mm"
include "syl.mm"
include "simp1.mm"
include "adantr.mm"
include "simp2.mm"
include "simpr.mm"
include "eqcomd.mm"
include "ccats1val2.mm"
include "syl3anc.mm"
include "a1d.mm"
include "ex.mm"
include "syld.mm"
include "imp32.mm"
include "cfzo.mm"
include "wb.mm"
include "eleq1.mm"
include "eqcoms.mm"
include "biimpd.mm"
include "a1i.mm"
include "com13.mm"
include "3ad2ant3.mm"
include "lbfzo0.mm"
include "sylibr.mm"
include "ccats1val1.mm"
include "eqtrd.mm"
include "jca31.mm"
include "eleq1a.mm"
include "impcom.mm"
include "syl2an23an.mm"
include "eqeq1d.mm"
include "com23.mm"
include "imp.mm"
include "jca.mm"
include "syldc.mm"
include "impbid.mm"
include "clwwlknwwlksnb.mm"
include "anbi1d.mm"
include "3anan32.mm"
include "3bitr4rd.mm"
include "wwlknon.mm"
include "3adant1.mm"
include "isclwwlknonOLD.mm"

theorem clwwlknonwwlknonbOLD
  let cG: class G
  let cN: class N
  let cV: class V
  let cW: class W
  let cX: class X
  let vi: setvar i
  assume clwwlknonwwlknonb.v: |- V = ( Vtx ` G )


  assert |- ( ( W e. Word V /\ X e. V /\ N e. NN ) -> ( W e. ( X ( ClWWalksNOn ` G ) N ) <-> ( W ++ <" X "> ) e. ( X ( N WWalksNOn G ) X ) ) )

  proof
    cW
    cV
    cword
    wcel
    #
    cX
    cV
    wcel
    #
    cN
    cn
    wcel
    #
    w3a
    #
    cW
    cX
    cs1
    #
    cconcat
    co
    #
    cN
    cG
    cwwlksn
    co
    #
    wcel
    #
    cc0
    @5
    cfv
    #
    cX
    wceq
    #
    cN
    @5
    cfv
    cX
    wceq
    #
    w3a
    #
    cW
    cN
    cG
    cclwwlkn
    co
    wcel
    #
    cc0
    cW
    cfv
    #
    cX
    wceq
    #
    wa
    #
    @5
    cX
    cX
    cN
    cG
    cwwlksnon
    co
    co
    wcel
    #
    cW
    cX
    cN
    cG
    cclwwlknon
    cfv
    co
    wcel
    #
    @3
    cW
    @13
    cs1
    #
    cconcat
    co
    #
    @6
    wcel
    #
    @14
    wa
    #
    @7
    @10
    wa
    #
    @9
    wa
    #
    @15
    @11
    @3
    @21
    @23
    @3
    @21
    @23
    @3
    @21
    wa
    #
    @7
    @10
    @9
    @21
    @7
    @3
    @14
    @20
    @7
    @14
    @19
    @5
    @6
    @14
    @18
    @4
    cW
    cconcat
    @13
    cX
    s1eq
    oveq2d
    eleq1d
    biimpac
    adantl
    @3
    @20
    @14
    @10
    @3
    @20
    cW
    chash
    cfv
    #
    cN
    wceq
    #
    @14
    @10
    wi
    #
    @3
    @0
    cN
    cn0
    wcel
    #
    wa
    #
    @20
    @26
    wi
    @0
    @2
    @29
    @1
    @2
    @28
    @0
    cN
    nnnn0
    #
    anim2i
    3adant2
    #
    cG
    cN
    cV
    cW
    @13
    wwlksnprcl
    syl
    #
    @3
    @26
    @27
    @3
    @26
    wa
    #
    @10
    @14
    @33
    @0
    @1
    cN
    @25
    wceq
    @10
    @3
    @0
    @26
    @0
    @1
    @2
    simp1
    #
    adantr
    @3
    @1
    @26
    @0
    @1
    @2
    simp2
    #
    adantr
    @33
    @25
    cN
    @3
    @26
    simpr
    eqcomd
    cX
    cN
    cV
    cW
    ccats1val2
    syl3anc
    a1d
    ex
    syld
    imp32
    @24
    @8
    @13
    cX
    @24
    @0
    @1
    cc0
    cc0
    @25
    cfzo
    co
    wcel
    #
    @8
    @13
    wceq
    #
    @3
    @0
    @21
    @34
    adantr
    @3
    @1
    @21
    @35
    adantr
    @24
    @25
    cn
    wcel
    #
    @36
    @3
    @20
    @14
    @38
    @3
    @20
    @26
    @14
    @38
    wi
    #
    @32
    @2
    @0
    @26
    @39
    wi
    @1
    @14
    @26
    @2
    @38
    @26
    @2
    @38
    wi
    wi
    @14
    @26
    @2
    @38
    @2
    @38
    wb
    cN
    @25
    cN
    @25
    cn
    eleq1
    eqcoms
    biimpd
    a1i
    com13
    3ad2ant3
    syld
    imp32
    @25
    lbfzo0
    #
    sylibr
    cX
    cc0
    cV
    cW
    ccats1val1
    #
    syl3anc
    @21
    @14
    @3
    @20
    @14
    simpr
    adantl
    eqtrd
    jca31
    ex
    @23
    @3
    @14
    @21
    @22
    @9
    @3
    @14
    wi
    #
    @7
    @9
    @42
    wi
    @10
    @7
    @3
    @9
    @14
    @7
    @3
    @9
    @14
    wi
    @7
    @3
    wa
    #
    @9
    @14
    @43
    @8
    @13
    cX
    @3
    @0
    @1
    @7
    @36
    @37
    @34
    @35
    @43
    @38
    @36
    @3
    @7
    @38
    @3
    @7
    @26
    @38
    @3
    @29
    @7
    @26
    wi
    @31
    cG
    cN
    cV
    cW
    cX
    wwlksnprcl
    syl
    @2
    @0
    @26
    @38
    wi
    @1
    cN
    cn
    @25
    eleq1a
    3ad2ant3
    syld
    impcom
    @40
    sylibr
    @41
    syl2an23an
    eqeq1d
    biimpd
    ex
    com23
    adantr
    imp
    @22
    @14
    @21
    wi
    #
    @9
    @7
    @44
    @10
    @7
    @14
    @21
    @7
    @14
    wa
    @20
    @14
    @14
    @7
    @20
    @14
    @5
    @19
    @6
    @14
    @4
    @18
    cW
    cconcat
    @4
    @18
    wceq
    cX
    @13
    cX
    @13
    s1eq
    eqcoms
    oveq2d
    eleq1d
    biimpac
    @7
    @14
    simpr
    jca
    ex
    adantr
    adantr
    syldc
    impbid
    @3
    @12
    @20
    @14
    @0
    @2
    @12
    @20
    wb
    @1
    cG
    cN
    cV
    cW
    clwwlknonwwlknonb.v
    clwwlknwwlksnb
    3adant2
    anbi1d
    @11
    @23
    wb
    @3
    @7
    @9
    @10
    3anan32
    a1i
    3bitr4rd
    @16
    @11
    wb
    @3
    cX
    cX
    cG
    cN
    @5
    wwlknon
    a1i
    @3
    @1
    @28
    wa
    #
    @17
    @15
    wb
    @1
    @2
    @45
    @0
    @2
    @28
    @1
    @30
    anim2i
    3adant1
    cG
    cN
    cV
    cW
    cX
    clwwlknonwwlknonb.v
    isclwwlknonOLD
    syl
    3bitr4rd
end

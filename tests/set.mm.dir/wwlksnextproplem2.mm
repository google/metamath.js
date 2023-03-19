include "wcel.mm"
include "cn0.mm"
include "cc0.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cop.mm"
include "csubstr.mm"
include "clsw.mm"
include "cfv.mm"
include "cpr.mm"
include "wi.mm"
include "cwwlksn.mm"
include "cvtx.mm"
include "cword.mm"
include "chash.mm"
include "wceq.mm"
include "cv.mm"
include "cfzo.mm"
include "wral.mm"
include "w3a.mm"
include "eqid.mm"
include "wwlknp.mm"
include "wa.mm"
include "fzonn0p1.mm"
include "adantl.mm"
include "fveq2.mm"
include "oveq1.mm"
include "fveq2d.mm"
include "preq12d.mm"
include "eleq1d.mm"
include "rspcv.mm"
include "syl.mm"
include "imp.mm"
include "wb.mm"
include "cmin.mm"
include "cfz.mm"
include "simpll.mm"
include "cz.mm"
include "cle.mm"
include "wbr.mm"
include "1zzd.mm"
include "lencl.mm"
include "nn0zd.mm"
include "ad2antrr.mm"
include "peano2nn0.mm"
include "3jca.mm"
include "nn0ge0.mm"
include "1red.mm"
include "nn0re.mm"
include "addge02d.mm"
include "mpbid.mm"
include "nn0red.mm"
include "lep1d.mm"
include "breq2.mm"
include "syl5ibrcom.mm"
include "a1i.mm"
include "com23.mm"
include "imp31.mm"
include "jca.mm"
include "elfz2.mm"
include "sylanbrc.mm"
include "swrd0fvlsw.mm"
include "nn0cn.mm"
include "1cnd.mm"
include "pncand.mm"
include "eqtrd.mm"
include "lsw.mm"
include "nn0cnd.mm"
include "sylan9eq.mm"
include "adantr.mm"
include "mpbird.mm"
include "exp31.mm"
include "3impia.mm"
include "eleq2s.mm"

theorem wwlksnextproplem2
  let cE: class E
  let cG: class G
  let cN: class N
  let cW: class W
  let cX: class X
  let vi: setvar i
  assume wwlksnextprop.x: |- X = ( ( N + 1 ) WWalksN G )
  assume wwlksnextprop.e: |- E = ( Edg ` G )


  assert |- ( ( W e. X /\ N e. NN0 ) -> { ( lastS ` ( W substr <. 0 , ( N + 1 ) >. ) ) , ( lastS ` W ) } e. E )

  proof
    cW
    cX
    wcel
    cN
    cn0
    wcel
    #
    cW
    cc0
    cN
    c1
    caddc
    co
    #
    cop
    csubstr
    co
    clsw
    cfv
    #
    cW
    clsw
    cfv
    #
    cpr
    #
    cE
    wcel
    #
    @0
    @5
    wi
    #
    cW
    @1
    cG
    cwwlksn
    co
    #
    cX
    cW
    @7
    wcel
    cW
    cG
    cvtx
    cfv
    #
    cword
    #
    wcel
    #
    cW
    chash
    cfv
    #
    @1
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
    #
    @14
    c1
    caddc
    co
    #
    cW
    cfv
    #
    cpr
    #
    cE
    wcel
    #
    vi
    cc0
    @1
    cfzo
    co
    #
    wral
    #
    w3a
    @6
    vi
    cE
    cG
    @1
    @8
    cW
    @8
    eqid
    wwlksnextprop.e
    wwlknp
    @10
    @13
    @21
    @6
    @10
    @13
    wa
    #
    @0
    @21
    @5
    @22
    @0
    @21
    @5
    @22
    @0
    wa
    #
    @21
    wa
    @5
    cN
    cW
    cfv
    #
    @1
    cW
    cfv
    #
    cpr
    #
    cE
    wcel
    #
    @23
    @21
    @27
    @23
    cN
    @20
    wcel
    #
    @21
    @27
    wi
    @0
    @28
    @22
    cN
    fzonn0p1
    adantl
    @19
    @27
    vi
    cN
    @20
    @14
    cN
    wceq
    #
    @18
    @26
    cE
    @29
    @15
    @24
    @17
    @25
    @14
    cN
    cW
    fveq2
    @29
    @16
    @1
    cW
    @14
    cN
    c1
    caddc
    oveq1
    fveq2d
    preq12d
    eleq1d
    rspcv
    syl
    imp
    @23
    @5
    @27
    wb
    @21
    @23
    @4
    @26
    cE
    @23
    @2
    @24
    @3
    @25
    @23
    @2
    @1
    c1
    cmin
    co
    #
    cW
    cfv
    #
    @24
    @23
    @10
    @1
    c1
    @11
    cfz
    co
    wcel
    #
    wa
    @2
    @31
    wceq
    @23
    @10
    @32
    @10
    @13
    @0
    simpll
    @23
    c1
    cz
    wcel
    #
    @11
    cz
    wcel
    #
    @1
    cz
    wcel
    #
    w3a
    c1
    @1
    cle
    wbr
    #
    @1
    @11
    cle
    wbr
    #
    wa
    @32
    @23
    @33
    @34
    @35
    @23
    1zzd
    @10
    @34
    @13
    @0
    @10
    @11
    @8
    cW
    lencl
    #
    nn0zd
    ad2antrr
    @0
    @35
    @22
    @0
    @1
    cN
    peano2nn0
    #
    nn0zd
    adantl
    3jca
    @23
    @36
    @37
    @0
    @36
    @22
    @0
    cc0
    cN
    cle
    wbr
    @36
    cN
    nn0ge0
    @0
    c1
    cN
    @0
    1red
    cN
    nn0re
    addge02d
    mpbid
    adantl
    @10
    @13
    @0
    @37
    @10
    @11
    cn0
    wcel
    #
    @13
    @0
    @37
    wi
    wi
    @38
    @40
    @0
    @13
    @37
    @0
    @13
    @37
    wi
    wi
    @40
    @0
    @37
    @13
    @1
    @12
    cle
    wbr
    @0
    @1
    @0
    @1
    @39
    nn0red
    lep1d
    @11
    @12
    @1
    cle
    breq2
    syl5ibrcom
    a1i
    com23
    syl
    imp31
    jca
    @1
    c1
    @11
    elfz2
    sylanbrc
    jca
    @1
    @8
    cW
    swrd0fvlsw
    syl
    @0
    @31
    @24
    wceq
    @22
    @0
    @30
    cN
    cW
    @0
    cN
    c1
    cN
    nn0cn
    @0
    1cnd
    #
    pncand
    fveq2d
    adantl
    eqtrd
    @23
    @3
    @11
    c1
    cmin
    co
    #
    cW
    cfv
    #
    @25
    @10
    @3
    @43
    wceq
    @13
    @0
    cW
    @9
    lsw
    ad2antrr
    @22
    @0
    @43
    @12
    c1
    cmin
    co
    #
    cW
    cfv
    #
    @25
    @13
    @43
    @45
    wceq
    @10
    @13
    @42
    @44
    cW
    @11
    @12
    c1
    cmin
    oveq1
    fveq2d
    adantl
    @0
    @44
    @1
    cW
    @0
    @1
    c1
    @0
    @1
    @39
    nn0cnd
    @41
    pncand
    fveq2d
    sylan9eq
    eqtrd
    preq12d
    eleq1d
    adantr
    mpbird
    exp31
    com23
    3impia
    syl
    wwlksnextprop.x
    eleq2s
    imp
end

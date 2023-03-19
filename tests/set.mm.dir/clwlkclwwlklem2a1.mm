include "cword.mm"
include "wcel.mm"
include "c2.mm"
include "chash.mm"
include "cfv.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "clsw.mm"
include "cc0.mm"
include "wceq.mm"
include "cv.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cpr.mm"
include "crn.mm"
include "cmin.mm"
include "cfzo.mm"
include "wral.mm"
include "csn.mm"
include "cun.mm"
include "wi.mm"
include "cn0.mm"
include "cc.mm"
include "lencl.mm"
include "nn0cn.mm"
include "peano2cnm.mm"
include "subid1d.mm"
include "oveq1d.mm"
include "sub1m1.mm"
include "eqtrd.mm"
include "3syl.mm"
include "adantr.mm"
include "oveq2d.mm"
include "raleqdv.mm"
include "biimpcd.mm"
include "adantl.mm"
include "impcom.mm"
include "lsw.mm"
include "2m1e1.mm"
include "a1i.mm"
include "eqcomd.mm"
include "syl.mm"
include "2cnd.mm"
include "1cnd.mm"
include "subsubd.mm"
include "fveq2d.mm"
include "wb.mm"
include "eqeq1.mm"
include "mpbid.mm"
include "preq2d.mm"
include "eleq1d.mm"
include "biimpd.mm"
include "ex.mm"
include "com13.mm"
include "cvv.mm"
include "ovexd.mm"
include "fveq2.mm"
include "oveq1.mm"
include "preq12d.mm"
include "ralunsn.mm"
include "mpbir2and.mm"
include "1e2m1.mm"
include "cuz.mm"
include "cz.mm"
include "nn0re.mm"
include "cr.mm"
include "2re.mm"
include "subge0d.mm"
include "biimprd.mm"
include "nn0z.mm"
include "2z.mm"
include "zsubcld.mm"
include "jctild.mm"
include "imp.mm"
include "elnn0z.mm"
include "sylibr.mm"
include "elnn0uz.mm"
include "sylib.mm"
include "fzosplitsn.mm"
include "mpbird.mm"

theorem clwlkclwwlklem2a1
  let cP: class P
  let vi: setvar i
  let cE: class E
  let cV: class V

  disjoint E i
  disjoint P i
  assert |- ( ( P e. Word V /\ 2 <_ ( # ` P ) ) -> ( ( ( lastS ` P ) = ( P ` 0 ) /\ ( A. i e. ( 0 ..^ ( ( ( ( # ` P ) - 1 ) - 0 ) - 1 ) ) { ( P ` i ) , ( P ` ( i + 1 ) ) } e. ran E /\ { ( P ` ( ( # ` P ) - 2 ) ) , ( P ` 0 ) } e. ran E ) ) -> A. i e. ( 0 ..^ ( ( # ` P ) - 1 ) ) { ( P ` i ) , ( P ` ( i + 1 ) ) } e. ran E ) )

  proof
    cP
    cV
    cword
    #
    wcel
    #
    c2
    cP
    chash
    cfv
    #
    cle
    wbr
    #
    wa
    #
    cP
    clsw
    cfv
    #
    cc0
    cP
    cfv
    #
    wceq
    #
    vi
    cv
    #
    cP
    cfv
    #
    @8
    c1
    caddc
    co
    #
    cP
    cfv
    #
    cpr
    #
    cE
    crn
    #
    wcel
    #
    vi
    cc0
    @2
    c1
    cmin
    co
    #
    cc0
    cmin
    co
    #
    c1
    cmin
    co
    #
    cfzo
    co
    #
    wral
    #
    @2
    c2
    cmin
    co
    #
    cP
    cfv
    #
    @6
    cpr
    #
    @13
    wcel
    #
    wa
    #
    wa
    #
    @14
    vi
    cc0
    @15
    cfzo
    co
    #
    wral
    #
    @4
    @25
    wa
    #
    @27
    @14
    vi
    cc0
    @20
    cfzo
    co
    #
    @20
    csn
    cun
    #
    wral
    #
    @28
    @31
    @14
    vi
    @29
    wral
    #
    @21
    @20
    c1
    caddc
    co
    #
    cP
    cfv
    #
    cpr
    #
    @13
    wcel
    #
    @25
    @4
    @32
    @24
    @4
    @32
    wi
    #
    @7
    @19
    @37
    @23
    @4
    @19
    @32
    @4
    @14
    vi
    @18
    @29
    @4
    @17
    @20
    cc0
    cfzo
    @1
    @17
    @20
    wceq
    #
    @3
    @1
    @2
    cn0
    wcel
    #
    @2
    cc
    wcel
    #
    @38
    cV
    cP
    lencl
    #
    @2
    nn0cn
    #
    @40
    @17
    @15
    c1
    cmin
    co
    @20
    @40
    @16
    @15
    c1
    cmin
    @40
    @15
    @2
    peano2cnm
    subid1d
    oveq1d
    @2
    sub1m1
    eqtrd
    3syl
    adantr
    oveq2d
    raleqdv
    biimpcd
    adantr
    adantl
    impcom
    @25
    @4
    @36
    @24
    @7
    @4
    @36
    wi
    #
    @23
    @7
    @43
    wi
    @19
    @4
    @7
    @23
    @36
    @4
    @7
    @23
    @36
    wi
    @4
    @7
    wa
    #
    @23
    @36
    @44
    @22
    @35
    @13
    @44
    @6
    @34
    @21
    @44
    @5
    @34
    wceq
    #
    @6
    @34
    wceq
    #
    @4
    @45
    @7
    @1
    @45
    @3
    @1
    @5
    @15
    cP
    cfv
    @34
    cP
    @0
    lsw
    @1
    @15
    @33
    cP
    @1
    @15
    @2
    c2
    c1
    cmin
    co
    #
    cmin
    co
    #
    @33
    @1
    c1
    @47
    @2
    cmin
    @1
    @47
    c1
    @47
    c1
    wceq
    @1
    2m1e1
    a1i
    eqcomd
    oveq2d
    @1
    @2
    c2
    c1
    @1
    @39
    @40
    @41
    @42
    syl
    @1
    2cnd
    @1
    1cnd
    subsubd
    #
    eqtrd
    fveq2d
    eqtrd
    adantr
    adantr
    @7
    @45
    @46
    wb
    @4
    @5
    @6
    @34
    eqeq1
    adantl
    mpbid
    preq2d
    eleq1d
    biimpd
    ex
    com13
    adantl
    impcom
    impcom
    @28
    @20
    cvv
    wcel
    @31
    @32
    @36
    wa
    wb
    @28
    @2
    c2
    cmin
    ovexd
    @14
    @36
    vi
    @29
    @20
    cvv
    @8
    @20
    wceq
    #
    @12
    @35
    @13
    @50
    @9
    @21
    @11
    @34
    @8
    @20
    cP
    fveq2
    @50
    @10
    @33
    cP
    @8
    @20
    c1
    caddc
    oveq1
    fveq2d
    preq12d
    eleq1d
    ralunsn
    syl
    mpbir2and
    @28
    @14
    vi
    @26
    @30
    @4
    @26
    @30
    wceq
    @25
    @4
    @26
    cc0
    @33
    cfzo
    co
    #
    @30
    @1
    @26
    @51
    wceq
    @3
    @1
    @15
    @33
    cc0
    cfzo
    @1
    @15
    @48
    @33
    @1
    c1
    @47
    @2
    cmin
    c1
    @47
    wceq
    @1
    1e2m1
    a1i
    oveq2d
    @49
    eqtrd
    oveq2d
    adantr
    @4
    @20
    cc0
    cuz
    cfv
    wcel
    #
    @51
    @30
    wceq
    @4
    @20
    cn0
    wcel
    #
    @52
    @4
    @20
    cz
    wcel
    #
    cc0
    @20
    cle
    wbr
    #
    wa
    #
    @53
    @1
    @3
    @56
    @1
    @39
    @3
    @56
    wi
    @41
    @39
    @3
    @55
    @54
    @39
    @55
    @3
    @39
    @2
    c2
    @2
    nn0re
    c2
    cr
    wcel
    @39
    2re
    a1i
    subge0d
    biimprd
    @39
    @2
    c2
    @2
    nn0z
    c2
    cz
    wcel
    @39
    2z
    a1i
    zsubcld
    jctild
    syl
    imp
    @20
    elnn0z
    sylibr
    @20
    elnn0uz
    sylib
    cc0
    @20
    fzosplitsn
    syl
    eqtrd
    adantr
    raleqdv
    mpbird
    ex
end

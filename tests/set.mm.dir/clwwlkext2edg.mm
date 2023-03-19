include "cs1.mm"
include "cconcat.mm"
include "co.mm"
include "cclwwlkn.mm"
include "wcel.mm"
include "cword.mm"
include "c2.mm"
include "cuz.mm"
include "cfv.mm"
include "w3a.mm"
include "clsw.mm"
include "cpr.mm"
include "cc0.mm"
include "wa.mm"
include "cn.mm"
include "wi.mm"
include "clwwlknnn.mm"
include "cv.mm"
include "c1.mm"
include "caddc.mm"
include "chash.mm"
include "cmin.mm"
include "cfzo.mm"
include "wral.mm"
include "wceq.mm"
include "isclwwlknx.mm"
include "ige2m2fzo.mm"
include "3ad2ant3.mm"
include "adantr.mm"
include "wb.mm"
include "oveq1.mm"
include "oveq2d.mm"
include "eleq2d.mm"
include "adantl.mm"
include "mpbird.mm"
include "fveq2.mm"
include "fveq2d.mm"
include "preq12d.mm"
include "eleq1d.mm"
include "rspcv.mm"
include "syl.mm"
include "wrdlenccats1lenm1.mm"
include "eqcomd.mm"
include "sylan9eq.mm"
include "ex.mm"
include "3adant3.mm"
include "eluzelcn.mm"
include "1cnd.mm"
include "subsub4d.mm"
include "1p1e2.mm"
include "a1i.mm"
include "eqtr2d.mm"
include "syld.mm"
include "imp.mm"
include "c0.mm"
include "wne.mm"
include "simpl1.mm"
include "s1cl.mm"
include "3ad2ant2.mm"
include "clt.mm"
include "wbr.mm"
include "cz.mm"
include "cle.mm"
include "eluz2.mm"
include "cr.mm"
include "zre.mm"
include "1red.mm"
include "2re.mm"
include "simpl.mm"
include "1lt2.mm"
include "simpr.mm"
include "ltletrd.mm"
include "id.mm"
include "posdifd.mm"
include "mpbid.mm"
include "3imp.mm"
include "sylbi.mm"
include "ad2antlr.mm"
include "breq2.mm"
include "hashneq0.mm"
include "3adantl2.mm"
include "3jca.mm"
include "ccatval1lsw.mm"
include "eqtrd.mm"
include "2m1e1.mm"
include "2cnd.mm"
include "subsubd.mm"
include "eqeq2.mm"
include "syl5ibrcom.mm"
include "ccatws1ls.mm"
include "sylibd.mm"
include "com13.mm"
include "imp31.mm"
include "lswccats1.mm"
include "ccatfv0.mm"
include "syl3anc.mm"
include "impcom.mm"
include "biimpcd.mm"
include "impl.mm"
include "jca.mm"
include "syl6bi.mm"
include "mpcom.mm"

theorem clwwlkext2edg
  let cE: class E
  let cG: class G
  let cN: class N
  let cV: class V
  let cW: class W
  let cZ: class Z
  let vi: setvar i
  assume clwwlkext2edg.v: |- V = ( Vtx ` G )
  assume clwwlkext2edg.e: |- E = ( Edg ` G )


  assert |- ( ( ( W e. Word V /\ Z e. V /\ N e. ( ZZ>= ` 2 ) ) /\ ( W ++ <" Z "> ) e. ( N ClWWalksN G ) ) -> ( { ( lastS ` W ) , Z } e. E /\ { Z , ( W ` 0 ) } e. E ) )

  proof
    cW
    cZ
    cs1
    #
    cconcat
    co
    #
    cN
    cG
    cclwwlkn
    co
    wcel
    #
    cW
    cV
    cword
    #
    wcel
    #
    cZ
    cV
    wcel
    #
    cN
    c2
    cuz
    cfv
    wcel
    #
    w3a
    #
    cW
    clsw
    cfv
    #
    cZ
    cpr
    #
    cE
    wcel
    #
    cZ
    cc0
    cW
    cfv
    #
    cpr
    #
    cE
    wcel
    #
    wa
    #
    cN
    cn
    wcel
    #
    @2
    @7
    @14
    wi
    #
    cG
    cN
    @1
    clwwlknnn
    @15
    @2
    @1
    @3
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
    cE
    wcel
    #
    vi
    cc0
    @1
    chash
    cfv
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
    @1
    clsw
    cfv
    #
    cc0
    @1
    cfv
    #
    cpr
    #
    cE
    wcel
    #
    w3a
    #
    @24
    cN
    wceq
    #
    wa
    #
    @16
    vi
    cE
    cG
    cN
    cV
    @1
    clwwlkext2edg.v
    clwwlkext2edg.e
    isclwwlknx
    @34
    @7
    @14
    @34
    @7
    wa
    @10
    @13
    @32
    @33
    @7
    @10
    @27
    @17
    @33
    @7
    @10
    wi
    wi
    @31
    @7
    @33
    @27
    @10
    @7
    @33
    @27
    @10
    wi
    @7
    @33
    wa
    #
    @27
    cN
    c2
    cmin
    co
    #
    @1
    cfv
    #
    @36
    c1
    caddc
    co
    #
    @1
    cfv
    #
    cpr
    #
    cE
    wcel
    #
    @10
    @35
    @36
    @26
    wcel
    #
    @27
    @41
    wi
    @35
    @42
    @36
    cc0
    cN
    c1
    cmin
    co
    #
    cfzo
    co
    #
    wcel
    #
    @7
    @45
    @33
    @6
    @4
    @45
    @5
    cN
    ige2m2fzo
    3ad2ant3
    adantr
    @33
    @42
    @45
    wb
    @7
    @33
    @26
    @44
    @36
    @33
    @25
    @43
    cc0
    cfzo
    @24
    cN
    c1
    cmin
    oveq1
    #
    oveq2d
    eleq2d
    adantl
    mpbird
    @23
    @41
    vi
    @36
    @26
    @18
    @36
    wceq
    #
    @22
    @40
    cE
    @47
    @19
    @37
    @21
    @39
    @18
    @36
    @1
    fveq2
    @47
    @20
    @38
    @1
    @18
    @36
    c1
    caddc
    oveq1
    fveq2d
    preq12d
    eleq1d
    rspcv
    syl
    @35
    @40
    @9
    cE
    @35
    @37
    @8
    @39
    cZ
    @35
    @37
    cW
    chash
    cfv
    #
    c1
    cmin
    co
    #
    @1
    cfv
    #
    @8
    @35
    @36
    @49
    @1
    @7
    @33
    @36
    @49
    wceq
    #
    @7
    @33
    @48
    @43
    wceq
    #
    @51
    @4
    @5
    @33
    @52
    wi
    @6
    @4
    @5
    wa
    #
    @33
    @52
    @53
    @33
    @48
    @25
    @43
    @4
    @48
    @25
    wceq
    @5
    @4
    @25
    @48
    cZ
    cV
    cW
    wrdlenccats1lenm1
    eqcomd
    adantr
    @46
    sylan9eq
    ex
    3adant3
    #
    @7
    @52
    @51
    @7
    @52
    @36
    @43
    c1
    cmin
    co
    #
    @49
    @6
    @4
    @36
    @55
    wceq
    @5
    @6
    @55
    cN
    c1
    c1
    caddc
    co
    #
    cmin
    co
    @36
    @6
    cN
    c1
    c1
    c2
    cN
    eluzelcn
    #
    @6
    1cnd
    #
    @58
    subsub4d
    @6
    @56
    c2
    cN
    cmin
    @56
    c2
    wceq
    @6
    1p1e2
    a1i
    oveq2d
    eqtr2d
    3ad2ant3
    @52
    @49
    @55
    @48
    @43
    c1
    cmin
    oveq1
    eqcomd
    sylan9eq
    ex
    syld
    imp
    fveq2d
    @35
    @4
    @0
    @3
    wcel
    #
    cW
    c0
    wne
    #
    w3a
    #
    @50
    @8
    wceq
    @7
    @33
    @61
    @7
    @33
    @52
    @61
    @54
    @7
    @52
    @61
    @7
    @52
    wa
    #
    @4
    @59
    @60
    @4
    @5
    @6
    @52
    simpl1
    #
    @7
    @59
    @52
    @5
    @4
    @59
    @6
    cZ
    cV
    s1cl
    3ad2ant2
    adantr
    #
    @4
    @6
    @52
    @60
    @5
    @4
    @6
    wa
    #
    @52
    wa
    #
    cc0
    @48
    clt
    wbr
    #
    @60
    @66
    @67
    cc0
    @43
    clt
    wbr
    #
    @6
    @68
    @4
    @52
    @6
    c2
    cz
    wcel
    #
    cN
    cz
    wcel
    #
    c2
    cN
    cle
    wbr
    #
    w3a
    @68
    c2
    cN
    eluz2
    @69
    @70
    @71
    @68
    @70
    @71
    @68
    wi
    #
    wi
    @69
    @70
    cN
    cr
    wcel
    #
    @72
    cN
    zre
    @73
    @71
    @68
    @73
    @71
    wa
    #
    c1
    cN
    clt
    wbr
    #
    @68
    @74
    c1
    c2
    cN
    @74
    1red
    c2
    cr
    wcel
    @74
    2re
    a1i
    @73
    @71
    simpl
    c1
    c2
    clt
    wbr
    @74
    1lt2
    a1i
    @73
    @71
    simpr
    ltletrd
    @73
    @75
    @68
    wb
    @71
    @73
    c1
    cN
    @73
    1red
    @73
    id
    posdifd
    adantr
    mpbid
    ex
    syl
    a1i
    3imp
    sylbi
    #
    ad2antlr
    @52
    @67
    @68
    wb
    #
    @65
    @48
    @43
    cc0
    clt
    breq2
    #
    adantl
    mpbird
    @65
    @67
    @60
    wb
    #
    @52
    @4
    @79
    @6
    cW
    @3
    hashneq0
    adantr
    adantr
    mpbid
    3adantl2
    3jca
    ex
    syld
    imp
    cW
    @0
    cV
    ccatval1lsw
    syl
    eqtrd
    @35
    @39
    @48
    @1
    cfv
    #
    cZ
    @35
    @38
    @48
    @1
    @7
    @33
    @38
    @48
    wceq
    #
    @7
    @33
    @52
    @81
    @54
    @7
    @81
    @52
    @38
    @43
    wceq
    #
    @6
    @4
    @82
    @5
    @6
    @43
    cN
    c2
    c1
    cmin
    co
    #
    cmin
    co
    @38
    @6
    c1
    @83
    cN
    cmin
    @6
    @83
    c1
    @83
    c1
    wceq
    @6
    2m1e1
    a1i
    eqcomd
    oveq2d
    @6
    cN
    c2
    c1
    @57
    @6
    2cnd
    @58
    subsubd
    eqtr2d
    3ad2ant3
    @48
    @43
    @38
    eqeq2
    syl5ibrcom
    syld
    imp
    fveq2d
    @35
    @53
    @80
    cZ
    wceq
    @7
    @53
    @33
    @4
    @5
    @53
    @6
    @53
    id
    3adant3
    #
    adantr
    cV
    cW
    cZ
    ccatws1ls
    syl
    eqtrd
    preq12d
    eleq1d
    sylibd
    ex
    com13
    3ad2ant2
    imp31
    @32
    @33
    @7
    @13
    @31
    @17
    @33
    @7
    wa
    #
    @13
    wi
    @27
    @85
    @31
    @13
    @85
    @30
    @12
    cE
    @7
    @33
    @30
    @12
    wceq
    #
    @7
    @33
    @52
    @86
    @54
    @7
    @52
    @86
    @62
    @28
    cZ
    @29
    @11
    @62
    @53
    @28
    cZ
    wceq
    @7
    @53
    @52
    @84
    adantr
    cZ
    cV
    cW
    lswccats1
    syl
    @62
    @4
    @59
    @67
    @29
    @11
    wceq
    @63
    @64
    @62
    @67
    @68
    @7
    @68
    @52
    @6
    @4
    @68
    @5
    @76
    3ad2ant3
    adantr
    @52
    @77
    @7
    @78
    adantl
    mpbird
    cW
    @0
    cV
    ccatfv0
    syl3anc
    preq12d
    ex
    syld
    impcom
    eleq1d
    biimpcd
    3ad2ant3
    impl
    jca
    ex
    syl6bi
    mpcom
    impcom
end

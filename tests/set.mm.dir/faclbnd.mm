include "cn0.mm"
include "wcel.mm"
include "cn.mm"
include "cc0.mm"
include "wceq.mm"
include "wo.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cexp.mm"
include "cfa.mm"
include "cfv.mm"
include "cmul.mm"
include "cle.mm"
include "wbr.mm"
include "elnn0.mm"
include "cv.mm"
include "wi.mm"
include "oveq1.mm"
include "oveq2d.mm"
include "fveq2.mm"
include "breq12d.mm"
include "imbi2d.mm"
include "nnre.mm"
include "nnge1.mm"
include "cuz.mm"
include "elnnuz.mm"
include "biimpi.mm"
include "leexp2ad.mm"
include "0p1e1.mm"
include "oveq2i.mm"
include "a1i.mm"
include "fac0.mm"
include "nnnn0.mm"
include "reexpcld.mm"
include "recnd.mm"
include "mulid1d.mm"
include "syl5eq.mm"
include "3brtr4d.mm"
include "wa.mm"
include "clt.mm"
include "cr.mm"
include "ad3antrrr.mm"
include "simpllr.mm"
include "peano2nn0.mm"
include "syl.mm"
include "faccld.mm"
include "nnred.mm"
include "remulcld.mm"
include "nn0re.mm"
include "peano2re.mm"
include "3syl.mm"
include "nngt0.mm"
include "0re.mm"
include "ltle.mm"
include "mpan.mm"
include "sylc.mm"
include "expge0d.mm"
include "simplr.mm"
include "simprr.mm"
include "lemul12ad.mm"
include "anandis.mm"
include "cc.mm"
include "nncn.mm"
include "expp1.mm"
include "syl2an.mm"
include "adantr.mm"
include "facp1.mm"
include "adantl.mm"
include "faccl.mm"
include "nncnd.mm"
include "nn0cn.mm"
include "peano2cn.mm"
include "mulassd.mm"
include "eqtr4d.mm"
include "exp32.mm"
include "com23.mm"
include "wb.mm"
include "nn0ltp1le.mm"
include "syl2anr.mm"
include "reexpcl.mm"
include "ad2antrr.mm"
include "remulcl.mm"
include "simpr.mm"
include "cz.mm"
include "ad2antlr.mm"
include "nn0zd.mm"
include "nnz.mm"
include "eluz.mm"
include "syl2anc.mm"
include "mpbird.mm"
include "anim12i.mm"
include "id.mm"
include "nn0ge0.mm"
include "nnge1d.mm"
include "lemulge11.mm"
include "letrd.mm"
include "ex.mm"
include "sylbid.mm"
include "a1dd.mm"
include "lelttric.mm"
include "mpjaod.mm"
include "expcom.mm"
include "a2d.mm"
include "nn0ind.mm"
include "impcom.mm"
include "nnnn0d.mm"
include "nn0ge0d.mm"
include "nn0p1nn.mm"
include "0expd.mm"
include "0exp0e1.mm"
include "oveq1i.mm"
include "mulid2d.mm"
include "oveq12.mm"
include "anidms.mm"
include "oveq1d.mm"
include "syl5ibr.mm"
include "imp.mm"
include "jaoian.mm"
include "sylanb.mm"

theorem faclbnd
  let cM: class M
  let cN: class N
  let vj: setvar j
  let vk: setvar k


  assert |- ( ( M e. NN0 /\ N e. NN0 ) -> ( M ^ ( N + 1 ) ) <_ ( ( M ^ M ) x. ( ! ` N ) ) )

  proof
    cM
    cn0
    wcel
    #
    cM
    cn
    wcel
    #
    cM
    cc0
    wceq
    #
    wo
    cN
    cn0
    wcel
    #
    cM
    cN
    c1
    caddc
    co
    #
    cexp
    co
    #
    cM
    cM
    cexp
    co
    #
    cN
    cfa
    cfv
    #
    cmul
    co
    #
    cle
    wbr
    #
    cM
    elnn0
    @1
    @3
    @9
    @2
    @3
    @1
    @9
    @1
    cM
    vj
    cv
    #
    c1
    caddc
    co
    #
    cexp
    co
    #
    @6
    @10
    cfa
    cfv
    #
    cmul
    co
    #
    cle
    wbr
    #
    wi
    @1
    cM
    cc0
    c1
    caddc
    co
    #
    cexp
    co
    #
    @6
    cc0
    cfa
    cfv
    #
    cmul
    co
    #
    cle
    wbr
    #
    wi
    @1
    cM
    vk
    cv
    #
    c1
    caddc
    co
    #
    cexp
    co
    #
    @6
    @21
    cfa
    cfv
    #
    cmul
    co
    #
    cle
    wbr
    #
    wi
    @1
    cM
    @22
    c1
    caddc
    co
    #
    cexp
    co
    #
    @6
    @22
    cfa
    cfv
    #
    cmul
    co
    #
    cle
    wbr
    #
    wi
    @1
    @9
    wi
    vj
    vk
    cN
    @10
    cc0
    wceq
    #
    @15
    @20
    @1
    @32
    @12
    @17
    @14
    @19
    cle
    @32
    @11
    @16
    cM
    cexp
    @10
    cc0
    c1
    caddc
    oveq1
    oveq2d
    @32
    @13
    @18
    @6
    cmul
    @10
    cc0
    cfa
    fveq2
    oveq2d
    breq12d
    imbi2d
    @10
    @21
    wceq
    #
    @15
    @26
    @1
    @33
    @12
    @23
    @14
    @25
    cle
    @33
    @11
    @22
    cM
    cexp
    @10
    @21
    c1
    caddc
    oveq1
    oveq2d
    @33
    @13
    @24
    @6
    cmul
    @10
    @21
    cfa
    fveq2
    oveq2d
    breq12d
    imbi2d
    @10
    @22
    wceq
    #
    @15
    @31
    @1
    @34
    @12
    @28
    @14
    @30
    cle
    @34
    @11
    @27
    cM
    cexp
    @10
    @22
    c1
    caddc
    oveq1
    oveq2d
    @34
    @13
    @29
    @6
    cmul
    @10
    @22
    cfa
    fveq2
    oveq2d
    breq12d
    imbi2d
    @10
    cN
    wceq
    #
    @15
    @9
    @1
    @35
    @12
    @5
    @14
    @8
    cle
    @35
    @11
    @4
    cM
    cexp
    @10
    cN
    c1
    caddc
    oveq1
    oveq2d
    @35
    @13
    @7
    @6
    cmul
    @10
    cN
    cfa
    fveq2
    oveq2d
    breq12d
    imbi2d
    @1
    cM
    c1
    cexp
    co
    #
    @6
    @17
    @19
    cle
    @1
    cM
    c1
    cM
    cM
    nnre
    #
    cM
    nnge1
    #
    @1
    cM
    c1
    cuz
    cfv
    wcel
    cM
    elnnuz
    biimpi
    leexp2ad
    @17
    @36
    wceq
    @1
    @16
    c1
    cM
    cexp
    0p1e1
    oveq2i
    a1i
    @1
    @19
    @6
    c1
    cmul
    co
    @6
    @18
    c1
    @6
    cmul
    fac0
    oveq2i
    @1
    @6
    @1
    @6
    @1
    cM
    cM
    @37
    cM
    nnnn0
    #
    reexpcld
    #
    recnd
    #
    mulid1d
    syl5eq
    3brtr4d
    @21
    cn0
    wcel
    #
    @1
    @26
    @31
    @1
    @42
    @26
    @31
    wi
    #
    @1
    @42
    wa
    #
    cM
    @22
    cle
    wbr
    #
    @43
    @22
    cM
    clt
    wbr
    #
    @44
    @26
    @45
    @31
    @44
    @26
    @45
    @31
    @44
    @26
    @45
    wa
    #
    wa
    @23
    cM
    cmul
    co
    #
    @25
    @22
    cmul
    co
    #
    @28
    @30
    cle
    @44
    @26
    @45
    @48
    @49
    cle
    wbr
    @44
    @26
    wa
    #
    @44
    @45
    wa
    #
    wa
    #
    @23
    @25
    cM
    @22
    @52
    cM
    @22
    @1
    cM
    cr
    wcel
    #
    @42
    @26
    @51
    @37
    ad3antrrr
    #
    @52
    @42
    @22
    cn0
    wcel
    #
    @1
    @42
    @26
    @51
    simpllr
    #
    @21
    peano2nn0
    #
    syl
    #
    reexpcld
    @52
    @6
    @24
    @52
    cM
    cM
    @54
    @1
    @0
    @42
    @26
    @51
    @39
    ad3antrrr
    reexpcld
    @52
    @24
    @52
    @21
    @56
    faccld
    nnred
    remulcld
    @54
    @52
    @42
    @21
    cr
    wcel
    #
    @22
    cr
    wcel
    #
    @56
    @21
    nn0re
    #
    @21
    peano2re
    #
    3syl
    @52
    cM
    @22
    @54
    @58
    @52
    @53
    cc0
    cM
    clt
    wbr
    #
    cc0
    cM
    cle
    wbr
    #
    @54
    @1
    @63
    @42
    @26
    @51
    cM
    nngt0
    ad3antrrr
    cc0
    cr
    wcel
    @53
    @63
    @64
    wi
    0re
    cc0
    cM
    ltle
    mpan
    sylc
    #
    expge0d
    @65
    @44
    @26
    @51
    simplr
    @50
    @44
    @45
    simprr
    lemul12ad
    anandis
    @44
    @28
    @48
    wceq
    #
    @47
    @1
    cM
    cc
    wcel
    @55
    @66
    @42
    cM
    nncn
    @57
    cM
    @22
    expp1
    syl2an
    adantr
    @44
    @30
    @49
    wceq
    @47
    @44
    @30
    @6
    @24
    @22
    cmul
    co
    #
    cmul
    co
    @49
    @44
    @29
    @67
    @6
    cmul
    @42
    @29
    @67
    wceq
    @1
    @21
    facp1
    adantl
    oveq2d
    @44
    @6
    @24
    @22
    @1
    @6
    cc
    wcel
    @42
    @41
    adantr
    @42
    @24
    cc
    wcel
    @1
    @42
    @24
    @21
    faccl
    nncnd
    adantl
    @42
    @22
    cc
    wcel
    #
    @1
    @42
    @21
    cc
    wcel
    @68
    @21
    nn0cn
    @21
    peano2cn
    syl
    adantl
    mulassd
    eqtr4d
    adantr
    3brtr4d
    exp32
    com23
    @44
    @46
    @31
    @26
    @44
    @46
    @27
    cM
    cle
    wbr
    #
    @31
    @42
    @55
    @0
    @46
    @69
    wb
    @1
    @57
    @39
    @22
    cM
    nn0ltp1le
    syl2anr
    @44
    @69
    @31
    @44
    @69
    wa
    #
    @28
    @6
    @30
    @44
    @28
    cr
    wcel
    #
    @69
    @1
    @53
    @27
    cn0
    wcel
    #
    @71
    @42
    @37
    @42
    @55
    @72
    @57
    @22
    peano2nn0
    syl
    #
    cM
    @27
    reexpcl
    syl2an
    adantr
    @1
    @6
    cr
    wcel
    #
    @42
    @69
    @40
    ad2antrr
    @44
    @30
    cr
    wcel
    #
    @69
    @1
    @74
    @29
    cr
    wcel
    #
    @75
    @42
    @40
    @42
    @29
    @42
    @22
    @57
    faccld
    #
    nnred
    #
    @6
    @29
    remulcl
    syl2an
    adantr
    @70
    cM
    @27
    cM
    @1
    @53
    @42
    @69
    @37
    ad2antrr
    @1
    c1
    cM
    cle
    wbr
    @42
    @69
    @38
    ad2antrr
    @70
    cM
    @27
    cuz
    cfv
    wcel
    #
    @69
    @44
    @69
    simpr
    @70
    @27
    cz
    wcel
    cM
    cz
    wcel
    #
    @79
    @69
    wb
    @70
    @27
    @42
    @72
    @1
    @69
    @73
    ad2antlr
    nn0zd
    @1
    @80
    @42
    @69
    cM
    nnz
    ad2antrr
    @27
    cM
    eluz
    syl2anc
    mpbird
    leexp2ad
    @44
    @6
    @30
    cle
    wbr
    #
    @69
    @44
    @74
    @76
    wa
    cc0
    @6
    cle
    wbr
    #
    c1
    @29
    cle
    wbr
    #
    wa
    @81
    @1
    @74
    @42
    @76
    @40
    @78
    anim12i
    @1
    @82
    @42
    @83
    @1
    @0
    @82
    @39
    @0
    cM
    cM
    cM
    nn0re
    @0
    id
    cM
    nn0ge0
    expge0d
    syl
    @42
    @29
    @77
    nnge1d
    anim12i
    @6
    @29
    lemulge11
    syl2anc
    adantr
    letrd
    ex
    sylbid
    a1dd
    @1
    @53
    @60
    @45
    @46
    wo
    @42
    @37
    @42
    @59
    @60
    @61
    @62
    syl
    cM
    @22
    lelttric
    syl2an
    mpjaod
    expcom
    a2d
    nn0ind
    impcom
    @2
    @3
    @9
    @3
    @9
    @2
    cc0
    @4
    cexp
    co
    #
    cc0
    cc0
    cexp
    co
    #
    @7
    cmul
    co
    #
    cle
    wbr
    @3
    cc0
    @7
    @84
    @86
    cle
    @3
    @7
    @3
    @7
    cN
    faccl
    #
    nnnn0d
    nn0ge0d
    @3
    @4
    cN
    nn0p1nn
    0expd
    @3
    @86
    c1
    @7
    cmul
    co
    @7
    @85
    c1
    @7
    cmul
    0exp0e1
    oveq1i
    @3
    @7
    @3
    @7
    @87
    nncnd
    mulid2d
    syl5eq
    3brtr4d
    @2
    @5
    @84
    @8
    @86
    cle
    cM
    cc0
    @4
    cexp
    oveq1
    @2
    @6
    @85
    @7
    cmul
    @2
    @6
    @85
    wceq
    cM
    cc0
    cM
    cc0
    cexp
    oveq12
    anidms
    oveq1d
    breq12d
    syl5ibr
    imp
    jaoian
    sylanb
end

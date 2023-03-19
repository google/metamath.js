include "csn.mm"
include "cun.mm"
include "cv.mm"
include "cfv.mm"
include "csu.mm"
include "cfa.mm"
include "cprod.mm"
include "cdiv.mm"
include "co.mm"
include "cmul.mm"
include "cn.mm"
include "c1.mm"
include "cdif.mm"
include "nfv.mm"
include "nfcv.mm"
include "cfn.mm"
include "wcel.mm"
include "wss.mm"
include "ssfi.mm"
include "syl2anc.mm"
include "wn.mm"
include "eldifn.mm"
include "syl.mm"
include "wa.mm"
include "cn0.mm"
include "wf.mm"
include "cmap.mm"
include "elmapi.mm"
include "adantr.mm"
include "elun1.mm"
include "adantl.mm"
include "ffvelrnd.mm"
include "faccld.mm"
include "nncnd.mm"
include "wceq.mm"
include "fveq2.mm"
include "fveq2d.mm"
include "snidg.mm"
include "elun2.mm"
include "fprodsplitsn.mm"
include "oveq2d.mm"
include "eldifad.mm"
include "snssi.mm"
include "unssd.mm"
include "ffvelrnda.mm"
include "fsumnn0cl.mm"
include "fprodclf.mm"
include "mulcld.mm"
include "nnne0d.mm"
include "fprodn0.mm"
include "mulne0d.mm"
include "divcld.mm"
include "mulid2d.mm"
include "eqcomd.mm"
include "cc0.mm"
include "wne.mm"
include "nnne0.mm"
include "dividd.mm"
include "mulcomd.mm"
include "divdiv1d.mm"
include "eqtrd.mm"
include "oveq12d.mm"
include "divmul13d.mm"
include "3eqtrd.mm"
include "cbc.mm"
include "cmin.mm"
include "csb.mm"
include "caddc.mm"
include "nfcsb1v.mm"
include "nn0cnd.mm"
include "csbeq1a.mm"
include "cc.mm"
include "csbfv.mm"
include "a1i.mm"
include "eqeltrd.mm"
include "fsumsplitsn.mm"
include "oveq1d.mm"
include "pncan2d.mm"
include "3eqtrrd.mm"
include "cfz.mm"
include "cz.mm"
include "w3a.mm"
include "cle.mm"
include "wbr.mm"
include "0zd.mm"
include "nn0zd.mm"
include "3jca.mm"
include "nn0ge0d.mm"
include "breqtrd.mm"
include "nn0red.mm"
include "cr.mm"
include "addge01d.mm"
include "mpbid.mm"
include "jca32.mm"
include "elfz2.mm"
include "sylibr.mm"
include "bcval2.mm"
include "bccl2.mm"
include "wral.mm"
include "cres.mm"
include "ssun1.mm"
include "elmapssres.mm"
include "fveq1.mm"
include "fvres.mm"
include "sumeq2dv.mm"
include "prodeq2dv.mm"
include "eleq1d.mm"
include "rspccva.mm"
include "nnmulcld.mm"

theorem mccllem
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let vk: setvar k
  let vb: setvar b
  assume mccllem.a: |- ( ph -> A e. Fin )
  assume mccllem.c: |- ( ph -> C C_ A )
  assume mccllem.d: |- ( ph -> D e. ( A \ C ) )
  assume mccllem.b: |- ( ph -> B e. ( NN0 ^m ( C u. { D } ) ) )
  assume mccllem.6: |- ( ph -> A. b e. ( NN0 ^m C ) ( ( ! ` sum_ k e. C ( b ` k ) ) / prod_ k e. C ( ! ` ( b ` k ) ) ) e. NN )

  disjoint A k
  disjoint B b
  disjoint B k
  disjoint b k
  disjoint C b
  disjoint C k
  disjoint D k
  disjoint k ph
  assert |- ( ph -> ( ( ! ` sum_ k e. ( C u. { D } ) ( B ` k ) ) / prod_ k e. ( C u. { D } ) ( ! ` ( B ` k ) ) ) e. NN )

  proof
    wph
    cC
    cD
    csn
    #
    cun
    #
    vk
    cv
    #
    cB
    cfv
    #
    vk
    csu
    #
    cfa
    cfv
    #
    @1
    @3
    cfa
    cfv
    #
    vk
    cprod
    #
    cdiv
    co
    #
    @5
    cD
    cB
    cfv
    #
    cfa
    cfv
    #
    cdiv
    co
    #
    cC
    @3
    vk
    csu
    #
    cfa
    cfv
    #
    cdiv
    co
    #
    @13
    cC
    @6
    vk
    cprod
    #
    cdiv
    co
    #
    cmul
    co
    #
    cn
    wph
    @8
    @5
    @15
    @10
    cmul
    co
    #
    cdiv
    co
    #
    c1
    @19
    cmul
    co
    #
    @17
    wph
    @7
    @18
    @5
    cdiv
    wph
    cC
    cD
    @6
    @10
    vk
    cA
    cC
    cdif
    #
    wph
    vk
    nfv
    #
    vk
    @10
    nfcv
    wph
    cA
    cfn
    wcel
    #
    cC
    cA
    wss
    cC
    cfn
    wcel
    mccllem.a
    mccllem.c
    cA
    cC
    ssfi
    syl2anc
    #
    mccllem.d
    wph
    cD
    @21
    wcel
    #
    cD
    cC
    wcel
    wn
    mccllem.d
    cD
    cA
    cC
    eldifn
    syl
    #
    wph
    @2
    cC
    wcel
    #
    wa
    #
    @6
    @28
    @3
    @28
    @1
    cn0
    @2
    cB
    wph
    @1
    cn0
    cB
    wf
    #
    @27
    wph
    cB
    cn0
    @1
    cmap
    co
    wcel
    #
    @29
    mccllem.b
    cB
    cn0
    @1
    elmapi
    syl
    #
    adantr
    @27
    @2
    @1
    wcel
    wph
    @2
    cC
    @0
    elun1
    adantl
    ffvelrnd
    #
    faccld
    #
    nncnd
    #
    @2
    cD
    wceq
    @3
    @9
    cfa
    @2
    cD
    cB
    fveq2
    fveq2d
    wph
    @10
    wph
    @9
    wph
    @1
    cn0
    cD
    cB
    @31
    wph
    cD
    @0
    wcel
    #
    cD
    @1
    wcel
    wph
    @25
    @35
    mccllem.d
    cD
    @21
    snidg
    syl
    cD
    @0
    cC
    elun2
    syl
    ffvelrnd
    #
    faccld
    #
    nncnd
    #
    fprodsplitsn
    oveq2d
    wph
    @20
    @19
    wph
    @19
    wph
    @5
    @18
    wph
    @5
    wph
    @4
    wph
    @1
    @3
    vk
    wph
    @23
    @1
    cA
    wss
    @1
    cfn
    wcel
    mccllem.a
    wph
    cC
    @0
    cA
    mccllem.c
    wph
    cD
    cA
    wcel
    @0
    cA
    wss
    wph
    cD
    cA
    cC
    mccllem.d
    eldifad
    #
    cD
    cA
    snssi
    syl
    unssd
    cA
    @1
    ssfi
    syl2anc
    wph
    @1
    cn0
    @2
    cB
    @31
    ffvelrnda
    fsumnn0cl
    #
    faccld
    nncnd
    #
    wph
    @15
    @10
    wph
    cC
    @6
    vk
    @22
    @24
    @34
    fprodclf
    #
    @38
    mulcld
    wph
    @15
    @10
    @42
    @38
    wph
    cC
    @6
    vk
    @24
    @34
    @28
    @6
    @33
    nnne0d
    fprodn0
    #
    wph
    @10
    @37
    nnne0d
    #
    mulne0d
    divcld
    mulid2d
    eqcomd
    wph
    @20
    @13
    @13
    cdiv
    co
    #
    @11
    @15
    cdiv
    co
    #
    cmul
    co
    @17
    wph
    c1
    @45
    @19
    @46
    cmul
    wph
    @45
    c1
    wph
    @13
    wph
    @13
    wph
    @12
    wph
    cC
    @3
    vk
    @24
    @32
    fsumnn0cl
    #
    faccld
    #
    nncnd
    #
    wph
    @13
    cn
    wcel
    @13
    cc0
    wne
    @48
    @13
    nnne0
    syl
    #
    dividd
    eqcomd
    wph
    @19
    @5
    @10
    @15
    cmul
    co
    #
    cdiv
    co
    #
    @46
    wph
    @18
    @51
    @5
    cdiv
    wph
    @15
    @10
    @42
    @38
    mulcomd
    oveq2d
    wph
    @46
    @52
    wph
    @5
    @10
    @15
    @41
    @38
    @42
    @44
    @43
    divdiv1d
    eqcomd
    eqtrd
    oveq12d
    wph
    @13
    @13
    @11
    @15
    @49
    @49
    wph
    @5
    @10
    @41
    @38
    @44
    divcld
    @42
    @50
    @43
    divmul13d
    eqtrd
    3eqtrd
    wph
    @14
    @16
    wph
    @14
    @4
    @12
    cbc
    co
    #
    cn
    wph
    @14
    @5
    @10
    @13
    cmul
    co
    #
    cdiv
    co
    @5
    @4
    @12
    cmin
    co
    #
    cfa
    cfv
    #
    @13
    cmul
    co
    #
    cdiv
    co
    #
    @53
    wph
    @5
    @10
    @13
    @41
    @38
    @49
    @44
    @50
    divdiv1d
    wph
    @54
    @57
    @5
    cdiv
    wph
    @10
    @56
    @13
    cmul
    wph
    @9
    @55
    cfa
    wph
    @55
    @12
    vk
    cD
    @3
    csb
    #
    caddc
    co
    #
    @12
    cmin
    co
    @59
    @9
    wph
    @4
    @60
    @12
    cmin
    wph
    cC
    cD
    @3
    @59
    vk
    cA
    @22
    vk
    cD
    @3
    nfcsb1v
    @24
    @39
    @26
    @28
    @3
    @32
    nn0cnd
    vk
    cD
    @3
    csbeq1a
    wph
    @59
    @9
    cc
    @59
    @9
    wceq
    wph
    vk
    cD
    cB
    csbfv
    a1i
    #
    wph
    @9
    @36
    nn0cnd
    eqeltrd
    #
    fsumsplitsn
    #
    oveq1d
    wph
    @12
    @59
    wph
    @12
    @47
    nn0cnd
    @62
    pncan2d
    @61
    3eqtrrd
    fveq2d
    oveq1d
    oveq2d
    wph
    @53
    @58
    wph
    @12
    cc0
    @4
    cfz
    co
    wcel
    #
    @53
    @58
    wceq
    wph
    cc0
    cz
    wcel
    #
    @4
    cz
    wcel
    #
    @12
    cz
    wcel
    #
    w3a
    #
    cc0
    @12
    cle
    wbr
    #
    @12
    @4
    cle
    wbr
    #
    wa
    wa
    @64
    wph
    @68
    @69
    @70
    wph
    @65
    @66
    @67
    wph
    0zd
    wph
    @4
    @40
    nn0zd
    wph
    @12
    @47
    nn0zd
    3jca
    wph
    @12
    @47
    nn0ge0d
    wph
    @12
    @60
    @4
    cle
    wph
    cc0
    @59
    cle
    wbr
    @12
    @60
    cle
    wbr
    wph
    cc0
    @9
    @59
    cle
    wph
    @9
    @36
    nn0ge0d
    wph
    @59
    @9
    @61
    eqcomd
    breqtrd
    wph
    @12
    @59
    wph
    @12
    @47
    nn0red
    wph
    @59
    @9
    cr
    @61
    wph
    @9
    @36
    nn0red
    eqeltrd
    addge01d
    mpbid
    wph
    @4
    @60
    @63
    eqcomd
    breqtrd
    jca32
    @12
    cc0
    @4
    elfz2
    sylibr
    #
    @12
    @4
    bcval2
    syl
    eqcomd
    3eqtrd
    wph
    @64
    @53
    cn
    wcel
    @71
    @12
    @4
    bccl2
    syl
    eqeltrd
    wph
    cC
    @2
    vb
    cv
    #
    cfv
    #
    vk
    csu
    #
    cfa
    cfv
    #
    cC
    @73
    cfa
    cfv
    #
    vk
    cprod
    #
    cdiv
    co
    #
    cn
    wcel
    #
    vb
    cn0
    cC
    cmap
    co
    #
    wral
    cB
    cC
    cres
    #
    @80
    wcel
    #
    @16
    cn
    wcel
    #
    mccllem.6
    wph
    @30
    cC
    @1
    wss
    #
    @82
    mccllem.b
    @84
    wph
    cC
    @0
    ssun1
    a1i
    cB
    cn0
    @1
    cC
    elmapssres
    syl2anc
    @79
    @83
    vb
    @81
    @80
    @72
    @81
    wceq
    #
    @78
    @16
    cn
    @85
    @75
    @13
    @77
    @15
    cdiv
    @85
    @74
    @12
    cfa
    @85
    cC
    @73
    @3
    vk
    @85
    @27
    wa
    #
    @73
    @2
    @81
    cfv
    #
    @3
    @85
    @73
    @87
    wceq
    @27
    @2
    @72
    @81
    fveq1
    adantr
    @27
    @87
    @3
    wceq
    @85
    @2
    cC
    cB
    fvres
    adantl
    eqtrd
    #
    sumeq2dv
    fveq2d
    @85
    cC
    @76
    @6
    vk
    @86
    @73
    @3
    cfa
    @88
    fveq2d
    prodeq2dv
    oveq12d
    eleq1d
    rspccva
    syl2anc
    nnmulcld
    eqeltrd
end

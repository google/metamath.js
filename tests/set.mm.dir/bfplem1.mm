include "clm.mm"
include "cfv.mm"
include "cdm.mm"
include "wcel.mm"
include "wbr.mm"
include "cms.mm"
include "cca.mm"
include "co.mm"
include "cdiv.mm"
include "cme.mm"
include "cmetmet.mm"
include "syl.mm"
include "c1.mm"
include "cn.mm"
include "nnuz.mm"
include "1zzd.mm"
include "algrf.mm"
include "cr.mm"
include "ffvelrnd.mm"
include "metcl.mm"
include "syl3anc.mm"
include "rerpdivcld.mm"
include "cv.mm"
include "caddc.mm"
include "cexp.mm"
include "cmul.mm"
include "cle.mm"
include "wi.mm"
include "wceq.mm"
include "fveq2.mm"
include "oveq1.mm"
include "fveq2d.mm"
include "oveq12d.mm"
include "oveq2.mm"
include "oveq2d.mm"
include "breq12d.mm"
include "imbi2d.mm"
include "leidd.mm"
include "algr0.mm"
include "1nn.mm"
include "algrp1.mm"
include "mpan2.mm"
include "eqtrd.mm"
include "rpred.mm"
include "recnd.mm"
include "exp1d.mm"
include "rpne0d.mm"
include "divcan1d.mm"
include "3brtr4d.mm"
include "wa.mm"
include "wral.mm"
include "ffvelrnda.mm"
include "wf.mm"
include "peano2nn.mm"
include "ffvelrn.mm"
include "syl2an.mm"
include "jca.mm"
include "ralrimivva.mm"
include "adantr.mm"
include "oveq1d.mm"
include "rspc2v.mm"
include "sylc.mm"
include "remulcld.mm"
include "adantl.mm"
include "nnnn0d.mm"
include "reexpcld.mm"
include "letr.mm"
include "mpand.mm"
include "cc0.mm"
include "clt.mm"
include "wb.mm"
include "cn0.mm"
include "nnnn0.mm"
include "reexpcl.mm"
include "rpgt0d.mm"
include "lemul1.mm"
include "syl112anc.mm"
include "cc.mm"
include "mulcomd.mm"
include "mulassd.mm"
include "expp1.mm"
include "eqtr4d.mm"
include "bitrd.mm"
include "sylan2.mm"
include "breq1d.mm"
include "3imtr4d.mm"
include "expcom.mm"
include "a2d.mm"
include "nnind.mm"
include "impcom.mm"
include "geomcau.mm"
include "cmetcau.mm"
include "syl2anc.mm"
include "cha.mm"
include "wfun.mm"
include "cxmt.mm"
include "metxmet.mm"
include "methaus.mm"
include "3syl.mm"
include "lmfun.mm"
include "funfvbrb.mm"
include "mpbid.mm"

theorem bfplem1
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cD: class D
  let cF: class F
  let cG: class G
  let cJ: class J
  let cK: class K
  let cX: class X
  let vj: setvar j
  let vk: setvar k
  let vz: setvar z
  let vw: setvar w
  assume bfp.2: |- ( ph -> D e. ( CMet ` X ) )
  assume bfp.3: |- ( ph -> X =/= (/) )
  assume bfp.4: |- ( ph -> K e. RR+ )
  assume bfp.5: |- ( ph -> K < 1 )
  assume bfp.6: |- ( ph -> F : X --> X )
  assume bfp.7: |- ( ( ph /\ ( x e. X /\ y e. X ) ) -> ( ( F ` x ) D ( F ` y ) ) <_ ( K x. ( x D y ) ) )
  assume bfp.8: |- J = ( MetOpen ` D )
  assume bfp.9: |- ( ph -> A e. X )
  assume bfp.10: |- G = seq 1 ( ( F o. 1st ) , ( NN X. { A } ) )

  disjoint x y
  disjoint D x
  disjoint D y
  disjoint G x
  disjoint G y
  disjoint J x
  disjoint J y
  disjoint ph x
  disjoint ph y
  disjoint F x
  disjoint F y
  disjoint K x
  disjoint K y
  disjoint X x
  disjoint X y
  disjoint j k
  disjoint j x
  disjoint j y
  disjoint j z
  disjoint D j
  disjoint k x
  disjoint k y
  disjoint k z
  disjoint D k
  disjoint x z
  disjoint y z
  disjoint D z
  disjoint G j
  disjoint G k
  disjoint G z
  disjoint J j
  disjoint J k
  disjoint J z
  disjoint j w
  disjoint j ph
  disjoint k w
  disjoint k ph
  disjoint w x
  disjoint w y
  disjoint ph w
  disjoint A j
  disjoint A k
  disjoint F j
  disjoint F k
  disjoint w z
  disjoint F w
  disjoint F z
  disjoint K j
  disjoint K k
  disjoint X j
  disjoint X k
  disjoint X w
  disjoint X z
  assert |- ( ph -> G ( ~~>t ` J ) ( ( ~~>t ` J ) ` G ) )

  proof
    wph
    cG
    cJ
    clm
    cfv
    #
    cdm
    wcel
    #
    cG
    cG
    @0
    cfv
    @0
    wbr
    #
    wph
    cD
    cX
    cms
    cfv
    wcel
    #
    cG
    cD
    cca
    cfv
    wcel
    @1
    bfp.2
    wph
    cA
    cA
    cF
    cfv
    #
    cD
    co
    #
    cK
    cdiv
    co
    #
    cK
    cD
    vk
    cG
    cX
    wph
    @3
    cD
    cX
    cme
    cfv
    wcel
    #
    bfp.2
    cD
    cX
    cmetmet
    syl
    #
    wph
    cA
    cG
    cX
    cF
    c1
    cn
    nnuz
    bfp.10
    wph
    1zzd
    #
    bfp.9
    bfp.6
    algrf
    #
    wph
    @5
    cK
    wph
    @7
    cA
    cX
    wcel
    @4
    cX
    wcel
    @5
    cr
    wcel
    @8
    bfp.9
    wph
    cX
    cX
    cA
    cF
    bfp.6
    bfp.9
    ffvelrnd
    cA
    @4
    cD
    cX
    metcl
    syl3anc
    #
    bfp.4
    rerpdivcld
    #
    bfp.4
    bfp.5
    vk
    cv
    #
    cn
    wcel
    #
    wph
    @13
    cG
    cfv
    #
    @13
    c1
    caddc
    co
    #
    cG
    cfv
    #
    cD
    co
    #
    @6
    cK
    @13
    cexp
    co
    #
    cmul
    co
    #
    cle
    wbr
    #
    wph
    vj
    cv
    #
    cG
    cfv
    #
    @22
    c1
    caddc
    co
    #
    cG
    cfv
    #
    cD
    co
    #
    @6
    cK
    @22
    cexp
    co
    #
    cmul
    co
    #
    cle
    wbr
    #
    wi
    wph
    c1
    cG
    cfv
    #
    c1
    c1
    caddc
    co
    #
    cG
    cfv
    #
    cD
    co
    #
    @6
    cK
    c1
    cexp
    co
    #
    cmul
    co
    #
    cle
    wbr
    #
    wi
    wph
    @21
    wi
    #
    wph
    @17
    @16
    c1
    caddc
    co
    #
    cG
    cfv
    #
    cD
    co
    #
    @6
    cK
    @16
    cexp
    co
    #
    cmul
    co
    #
    cle
    wbr
    #
    wi
    @37
    vj
    vk
    @13
    @22
    c1
    wceq
    #
    @29
    @36
    wph
    @44
    @26
    @33
    @28
    @35
    cle
    @44
    @23
    @30
    @25
    @32
    cD
    @22
    c1
    cG
    fveq2
    @44
    @24
    @31
    cG
    @22
    c1
    c1
    caddc
    oveq1
    fveq2d
    oveq12d
    @44
    @27
    @34
    @6
    cmul
    @22
    c1
    cK
    cexp
    oveq2
    oveq2d
    breq12d
    imbi2d
    @22
    @13
    wceq
    #
    @29
    @21
    wph
    @45
    @26
    @18
    @28
    @20
    cle
    @45
    @23
    @15
    @25
    @17
    cD
    @22
    @13
    cG
    fveq2
    @45
    @24
    @16
    cG
    @22
    @13
    c1
    caddc
    oveq1
    fveq2d
    oveq12d
    @45
    @27
    @19
    @6
    cmul
    @22
    @13
    cK
    cexp
    oveq2
    oveq2d
    breq12d
    imbi2d
    #
    @22
    @16
    wceq
    #
    @29
    @43
    wph
    @47
    @26
    @40
    @28
    @42
    cle
    @47
    @23
    @17
    @25
    @39
    cD
    @22
    @16
    cG
    fveq2
    @47
    @24
    @38
    cG
    @22
    @16
    c1
    caddc
    oveq1
    fveq2d
    oveq12d
    @47
    @27
    @41
    @6
    cmul
    @22
    @16
    cK
    cexp
    oveq2
    oveq2d
    breq12d
    imbi2d
    @46
    wph
    @5
    @5
    @33
    @35
    cle
    wph
    @5
    @11
    leidd
    wph
    @30
    cA
    @32
    @4
    cD
    wph
    cA
    cG
    cX
    cF
    c1
    cn
    nnuz
    bfp.10
    @9
    bfp.9
    algr0
    #
    wph
    @32
    @30
    cF
    cfv
    #
    @4
    wph
    c1
    cn
    wcel
    @32
    @49
    wceq
    1nn
    wph
    cA
    cG
    cX
    cF
    c1
    c1
    cn
    nnuz
    bfp.10
    @9
    bfp.9
    bfp.6
    algrp1
    mpan2
    wph
    @30
    cA
    cF
    @48
    fveq2d
    eqtrd
    oveq12d
    wph
    @35
    @6
    cK
    cmul
    co
    @5
    wph
    @34
    cK
    @6
    cmul
    wph
    cK
    wph
    cK
    wph
    cK
    bfp.4
    rpred
    #
    recnd
    #
    exp1d
    oveq2d
    wph
    @5
    cK
    wph
    @5
    @11
    recnd
    @51
    wph
    cK
    bfp.4
    rpne0d
    divcan1d
    eqtrd
    3brtr4d
    @14
    wph
    @21
    @43
    wph
    @14
    @21
    @43
    wi
    wph
    @14
    wa
    #
    cK
    @18
    cmul
    co
    #
    @42
    cle
    wbr
    #
    @15
    cF
    cfv
    #
    @17
    cF
    cfv
    #
    cD
    co
    #
    @42
    cle
    wbr
    #
    @21
    @43
    @52
    @57
    @53
    cle
    wbr
    #
    @54
    @58
    @52
    @15
    cX
    wcel
    #
    @17
    cX
    wcel
    #
    wa
    vx
    cv
    #
    cF
    cfv
    #
    vy
    cv
    #
    cF
    cfv
    #
    cD
    co
    #
    cK
    @62
    @64
    cD
    co
    #
    cmul
    co
    #
    cle
    wbr
    #
    vy
    cX
    wral
    vx
    cX
    wral
    #
    @59
    @52
    @60
    @61
    wph
    cn
    cX
    @13
    cG
    @10
    ffvelrnda
    #
    wph
    cn
    cX
    cG
    wf
    @16
    cn
    wcel
    #
    @61
    @14
    @10
    @13
    peano2nn
    #
    cn
    cX
    @16
    cG
    ffvelrn
    syl2an
    #
    jca
    wph
    @70
    @14
    wph
    @69
    vx
    vy
    cX
    cX
    bfp.7
    ralrimivva
    adantr
    @69
    @59
    @55
    @65
    cD
    co
    #
    cK
    @15
    @64
    cD
    co
    #
    cmul
    co
    #
    cle
    wbr
    vx
    vy
    @15
    @17
    cX
    cX
    @62
    @15
    wceq
    #
    @66
    @75
    @68
    @77
    cle
    @78
    @63
    @55
    @65
    cD
    @62
    @15
    cF
    fveq2
    oveq1d
    @78
    @67
    @76
    cK
    cmul
    @62
    @15
    @64
    cD
    oveq1
    oveq2d
    breq12d
    @64
    @17
    wceq
    #
    @75
    @57
    @77
    @53
    cle
    @79
    @65
    @56
    @55
    cD
    @64
    @17
    cF
    fveq2
    oveq2d
    @79
    @76
    @18
    cK
    cmul
    @64
    @17
    @15
    cD
    oveq2
    oveq2d
    breq12d
    rspc2v
    sylc
    @52
    @57
    cr
    wcel
    #
    @53
    cr
    wcel
    @42
    cr
    wcel
    @59
    @54
    wa
    @58
    wi
    @52
    @7
    @55
    cX
    wcel
    @56
    cX
    wcel
    @80
    wph
    @7
    @14
    @8
    adantr
    #
    @52
    cX
    cX
    @15
    cF
    wph
    cX
    cX
    cF
    wf
    @14
    bfp.6
    adantr
    #
    @71
    ffvelrnd
    @52
    cX
    cX
    @17
    cF
    @82
    @74
    ffvelrnd
    @55
    @56
    cD
    cX
    metcl
    syl3anc
    @52
    cK
    @18
    wph
    cK
    cr
    wcel
    #
    @14
    @50
    adantr
    #
    @52
    @7
    @60
    @61
    @18
    cr
    wcel
    #
    @81
    @71
    @74
    @15
    @17
    cD
    cX
    metcl
    syl3anc
    #
    remulcld
    @52
    @6
    @41
    wph
    @6
    cr
    wcel
    @14
    @12
    adantr
    #
    @52
    cK
    @16
    @84
    @52
    @16
    @14
    @72
    wph
    @73
    adantl
    nnnn0d
    reexpcld
    remulcld
    @57
    @53
    @42
    letr
    syl3anc
    mpand
    @52
    @21
    @18
    cK
    cmul
    co
    #
    @20
    cK
    cmul
    co
    #
    cle
    wbr
    #
    @54
    @52
    @85
    @20
    cr
    wcel
    @83
    cc0
    cK
    clt
    wbr
    #
    @21
    @90
    wb
    @86
    @52
    @6
    @19
    @87
    wph
    @83
    @13
    cn0
    wcel
    #
    @19
    cr
    wcel
    @14
    @50
    @13
    nnnn0
    #
    cK
    @13
    reexpcl
    syl2an
    #
    remulcld
    @84
    wph
    @91
    @14
    wph
    cK
    bfp.4
    rpgt0d
    adantr
    @18
    @20
    cK
    lemul1
    syl112anc
    @52
    @88
    @53
    @89
    @42
    cle
    @52
    @18
    cK
    @52
    @18
    @86
    recnd
    wph
    cK
    cc
    wcel
    #
    @14
    @51
    adantr
    #
    mulcomd
    @52
    @89
    @6
    @19
    cK
    cmul
    co
    #
    cmul
    co
    @42
    @52
    @6
    @19
    cK
    @52
    @6
    @87
    recnd
    @52
    @19
    @94
    recnd
    @96
    mulassd
    @52
    @41
    @97
    @6
    cmul
    wph
    @95
    @92
    @41
    @97
    wceq
    @14
    @51
    @93
    cK
    @13
    expp1
    syl2an
    oveq2d
    eqtr4d
    breq12d
    bitrd
    @52
    @40
    @57
    @42
    cle
    @52
    @17
    @55
    @39
    @56
    cD
    wph
    cA
    cG
    cX
    cF
    @13
    c1
    cn
    nnuz
    bfp.10
    @9
    bfp.9
    bfp.6
    algrp1
    @14
    wph
    @72
    @39
    @56
    wceq
    @73
    wph
    cA
    cG
    cX
    cF
    @16
    c1
    cn
    nnuz
    bfp.10
    @9
    bfp.9
    bfp.6
    algrp1
    sylan2
    oveq12d
    breq1d
    3imtr4d
    expcom
    a2d
    nnind
    impcom
    geomcau
    cD
    cG
    cJ
    cX
    bfp.8
    cmetcau
    syl2anc
    wph
    cJ
    cha
    wcel
    #
    @0
    wfun
    @1
    @2
    wb
    wph
    @7
    cD
    cX
    cxmt
    cfv
    wcel
    @98
    @8
    cD
    cX
    metxmet
    cD
    cJ
    cX
    bfp.8
    methaus
    3syl
    cJ
    lmfun
    cG
    @0
    funfvbrb
    3syl
    mpbid
end

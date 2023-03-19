include "clm.mm"
include "cfv.mm"
include "wcel.mm"
include "wceq.mm"
include "cv.mm"
include "wrex.mm"
include "ctopon.mm"
include "wbr.mm"
include "cme.mm"
include "cxmt.mm"
include "cms.mm"
include "cmetmet.mm"
include "syl.mm"
include "metxmet.mm"
include "mopntopon.mm"
include "3syl.mm"
include "bfplem1.mm"
include "lmcl.mm"
include "syl2anc.mm"
include "co.mm"
include "cc0.mm"
include "cle.mm"
include "caddc.mm"
include "crp.mm"
include "wral.mm"
include "wa.mm"
include "clt.mm"
include "c2.mm"
include "cdiv.mm"
include "cuz.mm"
include "cn.mm"
include "c1.mm"
include "adantr.mm"
include "nnuz.mm"
include "1zzd.mm"
include "eqidd.mm"
include "rphalfcl.mm"
include "adantl.mm"
include "lmmcvg.mm"
include "simpr.mm"
include "ralimi.mm"
include "cz.mm"
include "wi.mm"
include "nnz.mm"
include "uzid.mm"
include "fveq2.mm"
include "oveq1d.mm"
include "breq1d.mm"
include "rspcv.mm"
include "peano2uz.mm"
include "algrp1.mm"
include "adantlr.mm"
include "sylibd.mm"
include "jcad.mm"
include "cr.mm"
include "ad2antrr.mm"
include "wf.mm"
include "algrf.mm"
include "ffvelrnda.mm"
include "metcl.mm"
include "syl3anc.mm"
include "ffvelrnd.mm"
include "rpre.mm"
include "ad2antlr.mm"
include "lt2halves.mm"
include "readdcld.mm"
include "mettri2.mm"
include "syl13anc.mm"
include "cmul.mm"
include "rpred.mm"
include "remulcld.mm"
include "jca.mm"
include "ralrimivva.mm"
include "oveq1.mm"
include "oveq2d.mm"
include "breq12d.mm"
include "oveq2.mm"
include "rspc2v.mm"
include "sylc.mm"
include "1red.mm"
include "metge0.mm"
include "1re.mm"
include "ltle.mm"
include "sylancl.mm"
include "mpd.mm"
include "lemul1ad.mm"
include "recnd.mm"
include "mulid2d.mm"
include "breqtrd.mm"
include "letrd.mm"
include "leadd1dd.mm"
include "lelttr.mm"
include "mpand.mm"
include "3syld.mm"
include "syl5.mm"
include "rexlimdva.mm"
include "syl2an.mm"
include "addid2d.mm"
include "breqtrrd.mm"
include "ralrimiva.mm"
include "wb.mm"
include "0re.mm"
include "alrple.mm"
include "mpbird.mm"
include "letri3.mm"
include "mpbir2and.mm"
include "meteq0.mm"
include "mpbid.mm"
include "id.mm"
include "eqeq12d.mm"
include "rspcev.mm"

theorem bfplem2
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cD: class D
  let cF: class F
  let cG: class G
  let cJ: class J
  let cK: class K
  let cX: class X
  let vj: setvar j
  let vk: setvar k
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
  disjoint x z
  disjoint D x
  disjoint y z
  disjoint D y
  disjoint D z
  disjoint G x
  disjoint G y
  disjoint G z
  disjoint J x
  disjoint J y
  disjoint J z
  disjoint ph x
  disjoint ph y
  disjoint F x
  disjoint F y
  disjoint F z
  disjoint K x
  disjoint K y
  disjoint X x
  disjoint X y
  disjoint X z
  disjoint j k
  disjoint j x
  disjoint j y
  disjoint j z
  disjoint D j
  disjoint k x
  disjoint k y
  disjoint k z
  disjoint D k
  disjoint G j
  disjoint G k
  disjoint J j
  disjoint J k
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
  disjoint K j
  disjoint K k
  disjoint X j
  disjoint X k
  disjoint X w
  assert |- ( ph -> E. z e. X ( F ` z ) = z )

  proof
    wph
    cG
    cJ
    clm
    cfv
    #
    cfv
    #
    cX
    wcel
    #
    @1
    cF
    cfv
    #
    @1
    wceq
    #
    vz
    cv
    #
    cF
    cfv
    #
    @5
    wceq
    #
    vz
    cX
    wrex
    wph
    cJ
    cX
    ctopon
    cfv
    wcel
    #
    cG
    @1
    @0
    wbr
    #
    @2
    wph
    cD
    cX
    cme
    cfv
    wcel
    #
    cD
    cX
    cxmt
    cfv
    wcel
    #
    @8
    wph
    cD
    cX
    cms
    cfv
    wcel
    @10
    bfp.2
    cD
    cX
    cmetmet
    syl
    #
    cD
    cX
    metxmet
    #
    cD
    cJ
    cX
    bfp.8
    mopntopon
    3syl
    wph
    vx
    vy
    cA
    cD
    cF
    cG
    cJ
    cK
    cX
    bfp.2
    bfp.3
    bfp.4
    bfp.5
    bfp.6
    bfp.7
    bfp.8
    bfp.9
    bfp.10
    bfplem1
    #
    @1
    cG
    cJ
    cX
    lmcl
    syl2anc
    #
    wph
    @3
    @1
    cD
    co
    #
    cc0
    wceq
    #
    @4
    wph
    @17
    @16
    cc0
    cle
    wbr
    #
    cc0
    @16
    cle
    wbr
    #
    wph
    @18
    @16
    cc0
    vx
    cv
    #
    caddc
    co
    #
    cle
    wbr
    #
    vx
    crp
    wral
    #
    wph
    @22
    vx
    crp
    wph
    @20
    crp
    wcel
    #
    wa
    #
    @16
    @20
    @21
    cle
    @25
    @16
    @20
    clt
    wbr
    #
    @16
    @20
    cle
    wbr
    #
    @25
    vk
    cv
    #
    cG
    cfv
    #
    cX
    wcel
    #
    @29
    @1
    cD
    co
    #
    @20
    c2
    cdiv
    co
    #
    clt
    wbr
    #
    wa
    #
    vk
    vj
    cv
    #
    cuz
    cfv
    #
    wral
    #
    vj
    cn
    wrex
    @26
    @25
    @29
    cD
    @1
    @32
    vj
    vk
    cG
    cJ
    c1
    cX
    cn
    bfp.8
    @25
    @10
    @11
    wph
    @10
    @24
    @12
    adantr
    @13
    syl
    nnuz
    @25
    1zzd
    @25
    @28
    cn
    wcel
    wa
    @29
    eqidd
    wph
    @9
    @24
    @14
    adantr
    @24
    @32
    crp
    wcel
    wph
    @20
    rphalfcl
    adantl
    lmmcvg
    @25
    @37
    @26
    vj
    cn
    @37
    @33
    vk
    @36
    wral
    #
    @25
    @35
    cn
    wcel
    #
    wa
    #
    @26
    @34
    @33
    vk
    @36
    @30
    @33
    simpr
    ralimi
    @40
    @38
    @35
    cG
    cfv
    #
    @1
    cD
    co
    #
    @32
    clt
    wbr
    #
    @41
    cF
    cfv
    #
    @1
    cD
    co
    #
    @32
    clt
    wbr
    #
    wa
    #
    @42
    @45
    caddc
    co
    #
    @20
    clt
    wbr
    #
    @26
    @40
    @38
    @43
    @46
    @40
    @35
    cz
    wcel
    #
    @35
    @36
    wcel
    #
    @38
    @43
    wi
    @39
    @50
    @25
    @35
    nnz
    adantl
    #
    @35
    uzid
    #
    @33
    @43
    vk
    @35
    @36
    @28
    @35
    wceq
    #
    @31
    @42
    @32
    clt
    @54
    @29
    @41
    @1
    cD
    @28
    @35
    cG
    fveq2
    oveq1d
    breq1d
    rspcv
    3syl
    @40
    @38
    @35
    c1
    caddc
    co
    #
    cG
    cfv
    #
    @1
    cD
    co
    #
    @32
    clt
    wbr
    #
    @46
    @40
    @51
    @55
    @36
    wcel
    @38
    @58
    wi
    @40
    @50
    @51
    @52
    @53
    syl
    @35
    @35
    peano2uz
    @33
    @58
    vk
    @55
    @36
    @28
    @55
    wceq
    #
    @31
    @57
    @32
    clt
    @59
    @29
    @56
    @1
    cD
    @28
    @55
    cG
    fveq2
    oveq1d
    breq1d
    rspcv
    3syl
    @40
    @57
    @45
    @32
    clt
    @40
    @56
    @44
    @1
    cD
    wph
    @39
    @56
    @44
    wceq
    @24
    wph
    cA
    cG
    cX
    cF
    @35
    c1
    cn
    nnuz
    bfp.10
    wph
    1zzd
    #
    bfp.9
    bfp.6
    algrp1
    adantlr
    oveq1d
    breq1d
    sylibd
    jcad
    @40
    @42
    cr
    wcel
    #
    @45
    cr
    wcel
    #
    @20
    cr
    wcel
    #
    @47
    @49
    wi
    @40
    @10
    @41
    cX
    wcel
    #
    @2
    @61
    wph
    @10
    @24
    @39
    @12
    ad2antrr
    #
    @25
    cn
    cX
    @35
    cG
    wph
    cn
    cX
    cG
    wf
    @24
    wph
    cA
    cG
    cX
    cF
    c1
    cn
    nnuz
    bfp.10
    @60
    bfp.9
    bfp.6
    algrf
    adantr
    ffvelrnda
    #
    wph
    @2
    @24
    @39
    @15
    ad2antrr
    #
    @41
    @1
    cD
    cX
    metcl
    syl3anc
    #
    @40
    @10
    @44
    cX
    wcel
    #
    @2
    @62
    @65
    @40
    cX
    cX
    @41
    cF
    wph
    cX
    cX
    cF
    wf
    @24
    @39
    bfp.6
    ad2antrr
    #
    @66
    ffvelrnd
    #
    @67
    @44
    @1
    cD
    cX
    metcl
    syl3anc
    #
    @24
    @63
    wph
    @39
    @20
    rpre
    #
    ad2antlr
    #
    @42
    @45
    @20
    lt2halves
    syl3anc
    @40
    @16
    @48
    cle
    wbr
    #
    @49
    @26
    @40
    @16
    @44
    @3
    cD
    co
    #
    @45
    caddc
    co
    #
    @48
    wph
    @16
    cr
    wcel
    #
    @24
    @39
    wph
    @10
    @3
    cX
    wcel
    #
    @2
    @78
    @12
    wph
    cX
    cX
    @1
    cF
    bfp.6
    @15
    ffvelrnd
    #
    @15
    @3
    @1
    cD
    cX
    metcl
    syl3anc
    #
    ad2antrr
    #
    @40
    @76
    @45
    @40
    @10
    @69
    @79
    @76
    cr
    wcel
    @65
    @71
    @40
    cX
    cX
    @1
    cF
    @70
    @67
    ffvelrnd
    #
    @44
    @3
    cD
    cX
    metcl
    syl3anc
    #
    @72
    readdcld
    @40
    @42
    @45
    @68
    @72
    readdcld
    #
    @40
    @10
    @69
    @79
    @2
    @16
    @77
    cle
    wbr
    @65
    @71
    @83
    @67
    @3
    @1
    @44
    cD
    cX
    mettri2
    syl13anc
    @40
    @76
    @42
    @45
    @84
    @68
    @72
    @40
    @76
    cK
    @42
    cmul
    co
    #
    @42
    @84
    @40
    cK
    @42
    wph
    cK
    cr
    wcel
    #
    @24
    @39
    wph
    cK
    bfp.4
    rpred
    #
    ad2antrr
    #
    @68
    remulcld
    @68
    @40
    @64
    @2
    wa
    @20
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
    @20
    @91
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
    @76
    @86
    cle
    wbr
    #
    @40
    @64
    @2
    @66
    @67
    jca
    wph
    @97
    @24
    @39
    wph
    @96
    vx
    vy
    cX
    cX
    bfp.7
    ralrimivva
    ad2antrr
    @96
    @98
    @44
    @92
    cD
    co
    #
    cK
    @41
    @91
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
    @41
    @1
    cX
    cX
    @20
    @41
    wceq
    #
    @93
    @99
    @95
    @101
    cle
    @102
    @90
    @44
    @92
    cD
    @20
    @41
    cF
    fveq2
    oveq1d
    @102
    @94
    @100
    cK
    cmul
    @20
    @41
    @91
    cD
    oveq1
    oveq2d
    breq12d
    @91
    @1
    wceq
    #
    @99
    @76
    @101
    @86
    cle
    @103
    @92
    @3
    @44
    cD
    @91
    @1
    cF
    fveq2
    oveq2d
    @103
    @100
    @42
    cK
    cmul
    @91
    @1
    @41
    cD
    oveq2
    oveq2d
    breq12d
    rspc2v
    sylc
    @40
    @86
    c1
    @42
    cmul
    co
    @42
    cle
    @40
    cK
    c1
    @42
    @89
    @40
    1red
    @68
    @40
    @10
    @64
    @2
    cc0
    @42
    cle
    wbr
    @65
    @66
    @67
    @41
    @1
    cD
    cX
    metge0
    syl3anc
    wph
    cK
    c1
    cle
    wbr
    #
    @24
    @39
    wph
    cK
    c1
    clt
    wbr
    #
    @104
    bfp.5
    wph
    @87
    c1
    cr
    wcel
    @105
    @104
    wi
    @88
    1re
    cK
    c1
    ltle
    sylancl
    mpd
    ad2antrr
    lemul1ad
    @40
    @42
    @40
    @42
    @68
    recnd
    mulid2d
    breqtrd
    letrd
    leadd1dd
    letrd
    @40
    @78
    @48
    cr
    wcel
    @63
    @75
    @49
    wa
    @26
    wi
    @82
    @85
    @74
    @16
    @48
    @20
    lelttr
    syl3anc
    mpand
    3syld
    syl5
    rexlimdva
    mpd
    wph
    @78
    @63
    @26
    @27
    wi
    @24
    @81
    @73
    @16
    @20
    ltle
    syl2an
    mpd
    @25
    @20
    @25
    @20
    @24
    @63
    wph
    @73
    adantl
    recnd
    addid2d
    breqtrrd
    ralrimiva
    wph
    @78
    cc0
    cr
    wcel
    #
    @18
    @23
    wb
    @81
    0re
    vx
    @16
    cc0
    alrple
    sylancl
    mpbird
    wph
    @10
    @79
    @2
    @19
    @12
    @80
    @15
    @3
    @1
    cD
    cX
    metge0
    syl3anc
    wph
    @78
    @106
    @17
    @18
    @19
    wa
    wb
    @81
    0re
    @16
    cc0
    letri3
    sylancl
    mpbir2and
    wph
    @10
    @79
    @2
    @17
    @4
    wb
    @12
    @80
    @15
    @3
    @1
    cD
    cX
    meteq0
    syl3anc
    mpbid
    @7
    @4
    vz
    @1
    cX
    @5
    @1
    wceq
    #
    @6
    @3
    @5
    @1
    @5
    @1
    cF
    fveq2
    @107
    id
    eqeq12d
    rspcev
    syl2anc
end

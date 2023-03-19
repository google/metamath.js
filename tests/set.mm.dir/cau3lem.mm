include "cv.mm"
include "cfv.mm"
include "co.mm"
include "clt.mm"
include "wbr.mm"
include "wa.mm"
include "cuz.mm"
include "wral.mm"
include "wrex.mm"
include "crp.mm"
include "weq.mm"
include "breq2.mm"
include "anbi2d.mm"
include "rexralbidv.mm"
include "cbvralv.mm"
include "wcel.mm"
include "c2.mm"
include "cdiv.mm"
include "wi.mm"
include "rphalfcl.mm"
include "wceq.mm"
include "rspcv.mm"
include "syl.mm"
include "adantl.mm"
include "ralimi.mm"
include "r19.26.mm"
include "wb.mm"
include "fveq2.mm"
include "oveq1d.mm"
include "fveq2d.mm"
include "breq1d.mm"
include "anbi12d.mm"
include "biimpi.mm"
include "a1i.mm"
include "syl5bir.mm"
include "expdimp.mm"
include "cz.mm"
include "sseli.mm"
include "uzid.mm"
include "rspcva.mm"
include "sylan.mm"
include "adantll.mm"
include "jctild.mm"
include "simplll.mm"
include "simplrr.mm"
include "simplrl.mm"
include "syl3anc.mm"
include "cr.mm"
include "simpr.mm"
include "simpllr.mm"
include "rpred.mm"
include "syl122anc.mm"
include "sylbid.mm"
include "expd.mm"
include "impr.mm"
include "an32s.mm"
include "anassrs.mm"
include "expimpd.mm"
include "ralimdv.mm"
include "expr.mm"
include "wss.mm"
include "uzss.mm"
include "ssralv.mm"
include "sylan9.mm"
include "ralimdva.mm"
include "ex.mm"
include "com23.mm"
include "adantr.mm"
include "mpdd.mm"
include "sylan2.mm"
include "imdistanda.mm"
include "3imtr4g.mm"
include "reximdva.mm"
include "syld.mm"
include "ralrimdva.mm"
include "syl5bi.mm"
include "raleqbidv.mm"
include "ad2antlr.mm"
include "oveq2d.mm"
include "anim2i.mm"
include "w3a.mm"
include "3expia.mm"
include "sylc.mm"
include "ralbi.mm"
include "syl5bb.mm"
include "sylibd.mm"
include "impbid.mm"

theorem cau3lem
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let vx: setvar x
  let cD: class D
  let vj: setvar j
  let vk: setvar k
  let vm: setvar m
  let cF: class F
  let cG: class G
  let cZ: class Z
  let vz: setvar z
  assume cau3lem.1: |- Z C_ ZZ
  assume cau3lem.2: |- ( ta -> ps )
  assume cau3lem.3: |- ( ( F ` k ) = ( F ` j ) -> ( ps <-> ch ) )
  assume cau3lem.4: |- ( ( F ` k ) = ( F ` m ) -> ( ps <-> th ) )
  assume cau3lem.5: |- ( ( ph /\ ch /\ ps ) -> ( G ` ( ( F ` j ) D ( F ` k ) ) ) = ( G ` ( ( F ` k ) D ( F ` j ) ) ) )
  assume cau3lem.6: |- ( ( ph /\ th /\ ch ) -> ( G ` ( ( F ` m ) D ( F ` j ) ) ) = ( G ` ( ( F ` j ) D ( F ` m ) ) ) )
  assume cau3lem.7: |- ( ( ph /\ ( ps /\ th ) /\ ( ch /\ x e. RR ) ) -> ( ( ( G ` ( ( F ` k ) D ( F ` j ) ) ) < ( x / 2 ) /\ ( G ` ( ( F ` j ) D ( F ` m ) ) ) < ( x / 2 ) ) -> ( G ` ( ( F ` k ) D ( F ` m ) ) ) < x ) )

  disjoint k m
  disjoint ch k
  disjoint ch m
  disjoint k x
  disjoint D k
  disjoint m x
  disjoint D m
  disjoint D x
  disjoint F k
  disjoint F m
  disjoint F x
  disjoint j k
  disjoint j m
  disjoint j x
  disjoint j ph
  disjoint k ph
  disjoint m ph
  disjoint ph x
  disjoint G k
  disjoint G m
  disjoint G x
  disjoint m ps
  disjoint ps x
  disjoint ta x
  disjoint k th
  disjoint Z x
  disjoint j z
  disjoint k z
  disjoint m z
  disjoint x z
  disjoint D z
  disjoint F z
  disjoint G z
  disjoint ps z
  disjoint ta z
  disjoint Z z
  assert |- ( ph -> ( A. x e. RR+ E. j e. Z A. k e. ( ZZ>= ` j ) ( ta /\ ( G ` ( ( F ` k ) D ( F ` j ) ) ) < x ) <-> A. x e. RR+ E. j e. Z A. k e. ( ZZ>= ` j ) ( ta /\ A. m e. ( ZZ>= ` k ) ( G ` ( ( F ` k ) D ( F ` m ) ) ) < x ) ) )

  proof
    wph
    wta
    vk
    cv
    #
    cF
    cfv
    #
    vj
    cv
    #
    cF
    cfv
    #
    cD
    co
    #
    cG
    cfv
    #
    vx
    cv
    #
    clt
    wbr
    #
    wa
    #
    vk
    @2
    cuz
    cfv
    #
    wral
    #
    vj
    cZ
    wrex
    #
    vx
    crp
    wral
    #
    wta
    @1
    vm
    cv
    #
    cF
    cfv
    #
    cD
    co
    #
    cG
    cfv
    #
    @6
    clt
    wbr
    #
    vm
    @0
    cuz
    cfv
    #
    wral
    #
    wa
    vk
    @9
    wral
    #
    vj
    cZ
    wrex
    #
    vx
    crp
    wral
    #
    @12
    wta
    @5
    vz
    cv
    #
    clt
    wbr
    #
    wa
    #
    vk
    @9
    wral
    vj
    cZ
    wrex
    #
    vz
    crp
    wral
    #
    wph
    @22
    @11
    @26
    vx
    vz
    crp
    vx
    vz
    weq
    #
    @8
    @25
    vj
    vk
    cZ
    @9
    @28
    @7
    @24
    wta
    @6
    @23
    @5
    clt
    breq2
    anbi2d
    rexralbidv
    cbvralv
    wph
    @27
    @21
    vx
    crp
    wph
    @6
    crp
    wcel
    #
    wa
    #
    @27
    wta
    @5
    @6
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
    @9
    wral
    #
    vj
    cZ
    wrex
    #
    @21
    @29
    @27
    @35
    wi
    #
    wph
    @29
    @31
    crp
    wcel
    @36
    @6
    rphalfcl
    @26
    @35
    vz
    @31
    crp
    @23
    @31
    wceq
    #
    @25
    @33
    vj
    vk
    cZ
    @9
    @37
    @24
    @32
    wta
    @23
    @31
    @5
    clt
    breq2
    anbi2d
    rexralbidv
    rspcv
    syl
    adantl
    @30
    @34
    @20
    vj
    cZ
    @30
    @2
    cZ
    wcel
    #
    wa
    #
    wta
    vk
    @9
    wral
    #
    @32
    vk
    @9
    wral
    #
    wa
    @40
    @19
    vk
    @9
    wral
    #
    wa
    #
    @34
    @20
    @39
    @40
    @41
    @42
    @40
    @39
    wps
    vk
    @9
    wral
    #
    @41
    @42
    wi
    wta
    wps
    vk
    @9
    cau3lem.2
    ralimi
    #
    @39
    @44
    wa
    #
    @41
    wch
    wth
    @14
    @3
    cD
    co
    #
    cG
    cfv
    #
    @31
    clt
    wbr
    #
    wa
    #
    vm
    @9
    wral
    #
    wa
    #
    @42
    @46
    @41
    @51
    wch
    @39
    @44
    @41
    @51
    @44
    @41
    wa
    #
    wps
    @32
    wa
    #
    vk
    @9
    wral
    #
    @39
    @51
    wps
    @32
    vk
    @9
    r19.26
    #
    @55
    @51
    wi
    @39
    @55
    @51
    @54
    @50
    vk
    vm
    @9
    vk
    vm
    weq
    #
    wps
    wth
    @32
    @49
    @57
    @1
    @14
    wceq
    wps
    wth
    wb
    @0
    @13
    cF
    fveq2
    #
    cau3lem.4
    syl
    @57
    @5
    @48
    @31
    clt
    @57
    @4
    @47
    cG
    @57
    @1
    @14
    @3
    cD
    @58
    oveq1d
    fveq2d
    breq1d
    anbi12d
    cbvralv
    biimpi
    a1i
    syl5bir
    expdimp
    @38
    @44
    wch
    @30
    @38
    @2
    @9
    wcel
    #
    @44
    wch
    @38
    @2
    cz
    wcel
    @59
    cZ
    cz
    @2
    cau3lem.1
    sseli
    @2
    uzid
    syl
    #
    wps
    wch
    vk
    @2
    @9
    vk
    vj
    weq
    #
    @1
    @3
    wceq
    wps
    wch
    wb
    @0
    @2
    cF
    fveq2
    #
    cau3lem.3
    syl
    rspcva
    #
    sylan
    adantll
    jctild
    @39
    @44
    @41
    @52
    @42
    wi
    #
    @53
    @55
    @39
    @64
    @56
    @30
    @55
    @64
    wi
    @38
    @30
    @52
    @55
    @42
    @30
    @52
    @55
    @42
    wi
    @30
    @52
    wa
    #
    @54
    @19
    vk
    @9
    @65
    @0
    @9
    wcel
    #
    wa
    wps
    @32
    @19
    @65
    wps
    @66
    @32
    @19
    wi
    @65
    wps
    wa
    @32
    @17
    vm
    @9
    wral
    #
    @66
    @19
    @65
    wps
    @32
    @67
    @30
    @54
    @52
    @67
    @30
    @54
    wa
    #
    wch
    @51
    @67
    @68
    wch
    wa
    #
    @50
    @17
    vm
    @9
    @69
    wth
    @49
    @17
    @68
    wch
    wth
    @49
    @17
    wi
    #
    @30
    wch
    wth
    wa
    #
    @54
    @70
    @30
    @71
    wa
    #
    wps
    @32
    @70
    @72
    wps
    wa
    #
    @32
    @49
    @17
    @73
    @32
    @49
    wa
    @32
    @3
    @14
    cD
    co
    #
    cG
    cfv
    #
    @31
    clt
    wbr
    #
    wa
    #
    @17
    @73
    @49
    @76
    @32
    @73
    @48
    @75
    @31
    clt
    @73
    wph
    wth
    wch
    @48
    @75
    wceq
    wph
    @29
    @71
    wps
    simplll
    #
    @30
    wch
    wth
    wps
    simplrr
    #
    @30
    wch
    wth
    wps
    simplrl
    #
    cau3lem.6
    syl3anc
    breq1d
    anbi2d
    @73
    wph
    wps
    wth
    wch
    @6
    cr
    wcel
    @77
    @17
    wi
    @78
    @72
    wps
    simpr
    @79
    @80
    @73
    @6
    wph
    @29
    @71
    wps
    simpllr
    rpred
    cau3lem.7
    syl122anc
    sylbid
    expd
    impr
    an32s
    anassrs
    expimpd
    ralimdv
    impr
    an32s
    expr
    @66
    @18
    @9
    wss
    @67
    @19
    wi
    @2
    @0
    uzss
    @17
    vm
    @18
    @9
    ssralv
    syl
    sylan9
    an32s
    expimpd
    ralimdva
    ex
    com23
    adantr
    syl5bir
    expdimp
    mpdd
    sylan2
    imdistanda
    wta
    @32
    vk
    @9
    r19.26
    wta
    @19
    vk
    @9
    r19.26
    #
    3imtr4g
    reximdva
    syld
    ralrimdva
    syl5bi
    wph
    @21
    @11
    vx
    crp
    wph
    @20
    @10
    vj
    cZ
    wph
    @38
    wa
    @43
    @40
    @7
    vk
    @9
    wral
    #
    wa
    #
    @20
    @10
    @38
    wph
    @59
    @43
    @83
    wi
    @60
    wph
    @59
    wa
    #
    @40
    @42
    @82
    @40
    @84
    @44
    @42
    @82
    wi
    @45
    @84
    @44
    wa
    #
    @42
    @75
    @6
    clt
    wbr
    #
    vm
    @9
    wral
    #
    @82
    @59
    @42
    @87
    wi
    wph
    @44
    @19
    @87
    vk
    @2
    @9
    @61
    @17
    @86
    vm
    @18
    @9
    @0
    @2
    cuz
    fveq2
    @61
    @16
    @75
    @6
    clt
    @61
    @15
    @74
    cG
    @61
    @1
    @3
    @14
    cD
    @62
    oveq1d
    fveq2d
    breq1d
    raleqbidv
    rspcv
    ad2antlr
    @87
    @3
    @1
    cD
    co
    #
    cG
    cfv
    #
    @6
    clt
    wbr
    #
    vk
    @9
    wral
    #
    @85
    @82
    @86
    @90
    vm
    vk
    @9
    vm
    vk
    weq
    #
    @75
    @89
    @6
    clt
    @92
    @74
    @88
    cG
    @92
    @14
    @1
    @3
    cD
    @13
    @0
    cF
    fveq2
    oveq2d
    fveq2d
    breq1d
    cbvralv
    @85
    @90
    @7
    wb
    #
    vk
    @9
    wral
    #
    @91
    @82
    wb
    @85
    wph
    wch
    wa
    #
    @44
    @94
    wph
    @59
    @44
    @95
    @59
    @44
    wa
    wch
    wph
    @63
    anim2i
    anassrs
    @84
    @44
    simpr
    @95
    wps
    @93
    vk
    @9
    wph
    wch
    wps
    @93
    wph
    wch
    wps
    w3a
    @89
    @5
    @6
    clt
    cau3lem.5
    breq1d
    3expia
    ralimdv
    sylc
    @90
    @7
    vk
    @9
    ralbi
    syl
    syl5bb
    sylibd
    sylan2
    imdistanda
    sylan2
    @81
    wta
    @7
    vk
    @9
    r19.26
    3imtr4g
    reximdva
    ralimdv
    impbid
end

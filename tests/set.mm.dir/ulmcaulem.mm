include "cv.mm"
include "cfv.mm"
include "cmin.mm"
include "co.mm"
include "cabs.mm"
include "clt.mm"
include "wbr.mm"
include "wral.mm"
include "cuz.mm"
include "wrex.mm"
include "crp.mm"
include "wceq.mm"
include "breq2.mm"
include "ralbidv.mm"
include "rexralbidv.mm"
include "cbvralv.mm"
include "wcel.mm"
include "wa.mm"
include "c2.mm"
include "cdiv.mm"
include "wi.mm"
include "rphalfcl.mm"
include "rspcv.mm"
include "syl.mm"
include "adantl.mm"
include "fveq2.mm"
include "fveq1d.mm"
include "oveq1d.mm"
include "fveq2d.mm"
include "breq1d.mm"
include "biimpi.mm"
include "wss.mm"
include "uzss.mm"
include "ad2antlr.mm"
include "ssralv.mm"
include "r19.26.mm"
include "cc.mm"
include "cmap.mm"
include "wf.mm"
include "adantr.mm"
include "ad3antrrr.mm"
include "uztrn2.mm"
include "adantll.mm"
include "sylan.mm"
include "ffvelrnd.mm"
include "elmapi.mm"
include "ffvelrnda.mm"
include "ad2antrr.mm"
include "abssubd.mm"
include "biimpd.mm"
include "cr.mm"
include "ffvelrn.mm"
include "syl2an.mm"
include "anassrs.mm"
include "rpre.mm"
include "abs3lem.mm"
include "syl22anc.mm"
include "sylan2d.mm"
include "ralimdva.mm"
include "syl5bir.mm"
include "expdimp.mm"
include "an32s.mm"
include "syld.mm"
include "impancom.mm"
include "ex.mm"
include "com23.mm"
include "mpdi.mm"
include "reximdva.mm"
include "ralrimdva.mm"
include "syl5bi.mm"
include "cz.mm"
include "eluzelz.mm"
include "eleq2s.mm"
include "uzid.mm"
include "raleqbidv.mm"
include "oveq2d.mm"
include "ralbidva.mm"
include "syl5bb.mm"
include "sylibd.mm"
include "ralimdv.mm"
include "impbid.mm"

theorem ulmcaulem
  let wph: wff ph
  let vx: setvar x
  let vz: setvar z
  let cS: class S
  let vj: setvar j
  let vk: setvar k
  let vm: setvar m
  let cF: class F
  let cM: class M
  let cV: class V
  let cZ: class Z
  let vg: setvar g
  let vn: setvar n
  let vp: setvar p
  let vq: setvar q
  let vr: setvar r
  let vv: setvar v
  let vw: setvar w
  let vy: setvar y
  assume ulmcau.z: |- Z = ( ZZ>= ` M )
  assume ulmcau.m: |- ( ph -> M e. ZZ )
  assume ulmcau.s: |- ( ph -> S e. V )
  assume ulmcau.f: |- ( ph -> F : Z --> ( CC ^m S ) )

  disjoint j k
  disjoint j m
  disjoint j x
  disjoint j z
  disjoint F j
  disjoint k m
  disjoint k x
  disjoint k z
  disjoint F k
  disjoint m x
  disjoint m z
  disjoint F m
  disjoint x z
  disjoint F x
  disjoint F z
  disjoint j ph
  disjoint k ph
  disjoint m ph
  disjoint ph x
  disjoint ph z
  disjoint S j
  disjoint S k
  disjoint S m
  disjoint S x
  disjoint S z
  disjoint Z j
  disjoint Z k
  disjoint Z m
  disjoint Z x
  disjoint Z z
  disjoint M j
  disjoint M k
  disjoint M z
  disjoint g j
  disjoint g k
  disjoint g m
  disjoint g n
  disjoint g p
  disjoint g q
  disjoint g r
  disjoint g v
  disjoint g w
  disjoint g x
  disjoint g y
  disjoint g z
  disjoint F g
  disjoint j n
  disjoint j p
  disjoint j q
  disjoint j r
  disjoint j v
  disjoint j w
  disjoint j y
  disjoint k n
  disjoint k p
  disjoint k q
  disjoint k r
  disjoint k v
  disjoint k w
  disjoint k y
  disjoint m n
  disjoint m p
  disjoint m q
  disjoint m r
  disjoint m v
  disjoint m w
  disjoint m y
  disjoint n p
  disjoint n q
  disjoint n r
  disjoint n v
  disjoint n w
  disjoint n x
  disjoint n y
  disjoint n z
  disjoint F n
  disjoint p q
  disjoint p r
  disjoint p v
  disjoint p w
  disjoint p x
  disjoint p y
  disjoint p z
  disjoint F p
  disjoint q r
  disjoint q v
  disjoint q w
  disjoint q x
  disjoint q y
  disjoint q z
  disjoint F q
  disjoint r v
  disjoint r w
  disjoint r x
  disjoint r y
  disjoint r z
  disjoint F r
  disjoint v w
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint F v
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint F w
  disjoint x y
  disjoint y z
  disjoint F y
  disjoint g ph
  disjoint n ph
  disjoint p ph
  disjoint ph q
  disjoint ph r
  disjoint ph v
  disjoint ph w
  disjoint ph y
  disjoint S g
  disjoint S n
  disjoint S p
  disjoint S q
  disjoint S r
  disjoint S v
  disjoint S w
  disjoint S y
  disjoint Z g
  disjoint Z n
  disjoint Z p
  disjoint Z q
  disjoint Z r
  disjoint Z v
  disjoint Z w
  disjoint Z y
  disjoint M p
  disjoint M q
  disjoint M r
  disjoint M w
  assert |- ( ph -> ( A. x e. RR+ E. j e. Z A. k e. ( ZZ>= ` j ) A. z e. S ( abs ` ( ( ( F ` k ) ` z ) - ( ( F ` j ) ` z ) ) ) < x <-> A. x e. RR+ E. j e. Z A. k e. ( ZZ>= ` j ) A. m e. ( ZZ>= ` k ) A. z e. S ( abs ` ( ( ( F ` k ) ` z ) - ( ( F ` m ) ` z ) ) ) < x ) )

  proof
    wph
    vz
    cv
    #
    vk
    cv
    #
    cF
    cfv
    #
    cfv
    #
    @0
    vj
    cv
    #
    cF
    cfv
    #
    cfv
    #
    cmin
    co
    #
    cabs
    cfv
    #
    vx
    cv
    #
    clt
    wbr
    #
    vz
    cS
    wral
    #
    vk
    @4
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
    @3
    @0
    vm
    cv
    #
    cF
    cfv
    #
    cfv
    #
    cmin
    co
    #
    cabs
    cfv
    #
    @9
    clt
    wbr
    #
    vz
    cS
    wral
    #
    vm
    @1
    cuz
    cfv
    #
    wral
    #
    vk
    @12
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
    @15
    @8
    vw
    cv
    #
    clt
    wbr
    #
    vz
    cS
    wral
    #
    vk
    @12
    wral
    vj
    cZ
    wrex
    #
    vw
    crp
    wral
    #
    wph
    @27
    @14
    @31
    vx
    vw
    crp
    @9
    @28
    wceq
    #
    @11
    @30
    vj
    vk
    cZ
    @12
    @33
    @10
    @29
    vz
    cS
    @9
    @28
    @8
    clt
    breq2
    ralbidv
    rexralbidv
    cbvralv
    wph
    @32
    @26
    vx
    crp
    wph
    @9
    crp
    wcel
    #
    wa
    #
    @32
    @8
    @9
    c2
    cdiv
    co
    #
    clt
    wbr
    #
    vz
    cS
    wral
    #
    vk
    @12
    wral
    #
    vj
    cZ
    wrex
    #
    @26
    @34
    @32
    @40
    wi
    #
    wph
    @34
    @36
    crp
    wcel
    @41
    @9
    rphalfcl
    @31
    @40
    vw
    @36
    crp
    @28
    @36
    wceq
    #
    @30
    @38
    vj
    vk
    cZ
    @12
    @42
    @29
    @37
    vz
    cS
    @28
    @36
    @8
    clt
    breq2
    ralbidv
    rexralbidv
    rspcv
    syl
    adantl
    @35
    @39
    @25
    vj
    cZ
    @35
    @4
    cZ
    wcel
    #
    wa
    #
    @39
    @18
    @6
    cmin
    co
    #
    cabs
    cfv
    #
    @36
    clt
    wbr
    #
    vz
    cS
    wral
    #
    vm
    @12
    wral
    #
    @25
    @39
    @49
    @38
    @48
    vk
    vm
    @12
    @1
    @16
    wceq
    #
    @37
    @47
    vz
    cS
    @50
    @8
    @46
    @36
    clt
    @50
    @7
    @45
    cabs
    @50
    @3
    @18
    @6
    cmin
    @50
    @0
    @2
    @17
    @1
    @16
    cF
    fveq2
    fveq1d
    oveq1d
    fveq2d
    breq1d
    ralbidv
    cbvralv
    biimpi
    @44
    @49
    @39
    @25
    @44
    @49
    @39
    @25
    wi
    @44
    @49
    wa
    @38
    @24
    vk
    @12
    @44
    @1
    @12
    wcel
    #
    @49
    @38
    @24
    wi
    @44
    @51
    wa
    #
    @38
    @49
    @24
    @52
    @38
    wa
    #
    @49
    @48
    vm
    @23
    wral
    #
    @24
    @53
    @23
    @12
    wss
    #
    @49
    @54
    wi
    @51
    @55
    @44
    @38
    @4
    @1
    uzss
    ad2antlr
    @48
    vm
    @23
    @12
    ssralv
    syl
    @53
    @48
    @22
    vm
    @23
    @52
    @16
    @23
    wcel
    #
    @38
    @48
    @22
    wi
    @52
    @56
    wa
    #
    @38
    @48
    @22
    @38
    @48
    wa
    @37
    @47
    wa
    #
    vz
    cS
    wral
    @57
    @22
    @37
    @47
    vz
    cS
    r19.26
    @57
    @58
    @21
    vz
    cS
    @57
    @0
    cS
    wcel
    #
    wa
    #
    @47
    @6
    @18
    cmin
    co
    #
    cabs
    cfv
    #
    @36
    clt
    wbr
    #
    @37
    @21
    @60
    @47
    @63
    @60
    @46
    @62
    @36
    clt
    @60
    @18
    @6
    @57
    cS
    cc
    @0
    @17
    @57
    @17
    cc
    cS
    cmap
    co
    #
    wcel
    cS
    cc
    @17
    wf
    @57
    cZ
    @64
    @16
    cF
    @35
    cZ
    @64
    cF
    wf
    #
    @43
    @51
    @56
    wph
    @65
    @34
    ulmcau.f
    adantr
    #
    ad3antrrr
    @52
    @1
    cZ
    wcel
    #
    @56
    @16
    cZ
    wcel
    @43
    @51
    @67
    @35
    cM
    @1
    @4
    cZ
    ulmcau.z
    uztrn2
    #
    adantll
    cM
    @16
    @1
    cZ
    ulmcau.z
    uztrn2
    sylan
    ffvelrnd
    @17
    cc
    cS
    elmapi
    syl
    ffvelrnda
    #
    @57
    cS
    cc
    @0
    @5
    @57
    @5
    @64
    wcel
    #
    cS
    cc
    @5
    wf
    #
    @44
    @70
    @51
    @56
    @35
    cZ
    @64
    @4
    cF
    @66
    ffvelrnda
    ad2antrr
    @5
    cc
    cS
    elmapi
    #
    syl
    ffvelrnda
    #
    abssubd
    breq1d
    biimpd
    @60
    @3
    cc
    wcel
    @18
    cc
    wcel
    @6
    cc
    wcel
    @9
    cr
    wcel
    #
    @37
    @63
    wa
    @21
    wi
    @57
    cS
    cc
    @0
    @2
    @57
    @2
    @64
    wcel
    #
    cS
    cc
    @2
    wf
    #
    @52
    @75
    @56
    @35
    @43
    @51
    @75
    @35
    @65
    @67
    @75
    @43
    @51
    wa
    #
    @66
    @68
    cZ
    @64
    @1
    cF
    ffvelrn
    #
    syl2an
    anassrs
    adantr
    @2
    cc
    cS
    elmapi
    #
    syl
    ffvelrnda
    @69
    @73
    @44
    @74
    @51
    @56
    @59
    @34
    @74
    wph
    @43
    @9
    rpre
    ad2antlr
    ad3antrrr
    @3
    @18
    @6
    @9
    abs3lem
    syl22anc
    sylan2d
    ralimdva
    syl5bir
    expdimp
    an32s
    ralimdva
    syld
    impancom
    an32s
    ralimdva
    ex
    com23
    mpdi
    reximdva
    syld
    ralrimdva
    syl5bi
    wph
    @26
    @14
    vx
    crp
    wph
    @25
    @13
    vj
    cZ
    wph
    @43
    wa
    #
    @25
    @62
    @9
    clt
    wbr
    #
    vz
    cS
    wral
    #
    vm
    @12
    wral
    #
    @13
    @80
    @4
    @12
    wcel
    #
    @25
    @83
    wi
    @43
    @84
    wph
    @43
    @4
    cz
    wcel
    #
    @84
    @85
    @4
    cM
    cuz
    cfv
    cZ
    cM
    @4
    eluzelz
    ulmcau.z
    eleq2s
    @4
    uzid
    syl
    adantl
    @24
    @83
    vk
    @4
    @12
    @1
    @4
    wceq
    #
    @22
    @82
    vm
    @23
    @12
    @1
    @4
    cuz
    fveq2
    @86
    @21
    @81
    vz
    cS
    @86
    @20
    @62
    @9
    clt
    @86
    @19
    @61
    cabs
    @86
    @3
    @6
    @18
    cmin
    @86
    @0
    @2
    @5
    @1
    @4
    cF
    fveq2
    fveq1d
    oveq1d
    fveq2d
    breq1d
    ralbidv
    raleqbidv
    rspcv
    syl
    @83
    @6
    @3
    cmin
    co
    #
    cabs
    cfv
    #
    @9
    clt
    wbr
    #
    vz
    cS
    wral
    #
    vk
    @12
    wral
    @80
    @13
    @82
    @90
    vm
    vk
    @12
    @16
    @1
    wceq
    #
    @81
    @89
    vz
    cS
    @91
    @62
    @88
    @9
    clt
    @91
    @61
    @87
    cabs
    @91
    @18
    @3
    @6
    cmin
    @91
    @0
    @17
    @2
    @16
    @1
    cF
    fveq2
    fveq1d
    oveq2d
    fveq2d
    breq1d
    ralbidv
    cbvralv
    @80
    @90
    @11
    vk
    @12
    @80
    @51
    wa
    #
    @89
    @10
    vz
    cS
    @92
    @59
    wa
    #
    @88
    @8
    @9
    clt
    @93
    @6
    @3
    @92
    cS
    cc
    @0
    @5
    @92
    @70
    @71
    @80
    @70
    @51
    wph
    cZ
    @64
    @4
    cF
    ulmcau.f
    ffvelrnda
    adantr
    @72
    syl
    ffvelrnda
    @92
    cS
    cc
    @0
    @2
    @92
    @75
    @76
    wph
    @43
    @51
    @75
    wph
    @65
    @67
    @75
    @77
    ulmcau.f
    @68
    @78
    syl2an
    anassrs
    @79
    syl
    ffvelrnda
    abssubd
    breq1d
    ralbidva
    ralbidva
    syl5bb
    sylibd
    reximdva
    ralimdv
    impbid
end

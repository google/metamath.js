include "cv.mm"
include "c2.mm"
include "cuz.mm"
include "cfv.mm"
include "wcel.mm"
include "wa.mm"
include "cmul.mm"
include "co.mm"
include "cfmtno.mm"
include "cdvds.mm"
include "wbr.mm"
include "caddc.mm"
include "cexp.mm"
include "c1.mm"
include "wceq.mm"
include "cn0.mm"
include "wrex.mm"
include "wi.mm"
include "cz.mm"
include "eluzelz.mm"
include "adantr.mm"
include "adantl.mm"
include "eluzge2nn0.mm"
include "fmtnonn.mm"
include "nnzd.mm"
include "syl.mm"
include "muldvds2.mm"
include "syl2an3an.mm"
include "muldvds1.mm"
include "pm2.27.mm"
include "ad2ant2lr.mm"
include "ad2ant2l.mm"
include "weq.mm"
include "oveq1.mm"
include "oveq1d.mm"
include "eqeq2d.mm"
include "cbvrexv.mm"
include "simpl.mm"
include "2nn0.mm"
include "a1i.mm"
include "nn0addcld.mm"
include "nn0expcld.mm"
include "nn0mulcld.mm"
include "simpr.mm"
include "nn0addcl.mm"
include "wb.mm"
include "eqidd.mm"
include "rspcedvd.mm"
include "cc.mm"
include "nn0cn.mm"
include "nn0cnd.mm"
include "mulcld.mm"
include "jca.mm"
include "muladd11r.mm"
include "w3a.mm"
include "3jca.mm"
include "adddir.mm"
include "eqcomd.mm"
include "oveq2d.mm"
include "mulassd.mm"
include "3eqtr4d.mm"
include "eqtrd.mm"
include "eqeq1d.mm"
include "rexbidva.mm"
include "mpbird.mm"
include "adantll.mm"
include "oveq12.mm"
include "ancoms.mm"
include "rexbidv.mm"
include "syl5ibrcom.mm"
include "expd.mm"
include "anassrs.mm"
include "rexlimdva.mm"
include "syl5bi.mm"
include "com23.mm"
include "impd.mm"
include "syl2and.mm"
include "exp32.mm"
include "syld.mm"
include "mpdd.mm"
include "expimpd.mm"

theorem fmtnofac2lem
  let vy: setvar y
  let vz: setvar z
  let vk: setvar k
  let cN: class N
  let cM: class M
  let vx: setvar x
  let vm: setvar m
  let vn: setvar n

  disjoint N k
  disjoint N y
  disjoint N z
  disjoint k y
  disjoint k z
  disjoint y z
  disjoint M k
  disjoint M x
  disjoint k x
  disjoint N m
  disjoint N n
  disjoint N x
  disjoint k m
  disjoint k n
  disjoint m n
  disjoint m x
  disjoint m y
  disjoint m z
  disjoint n x
  disjoint n y
  disjoint n z
  disjoint x y
  disjoint x z
  disjoint k x
  assert |- ( ( y e. ( ZZ>= ` 2 ) /\ z e. ( ZZ>= ` 2 ) ) -> ( ( ( ( N e. ( ZZ>= ` 2 ) /\ y || ( FermatNo ` N ) ) -> E. k e. NN0 y = ( ( k x. ( 2 ^ ( N + 2 ) ) ) + 1 ) ) /\ ( ( N e. ( ZZ>= ` 2 ) /\ z || ( FermatNo ` N ) ) -> E. k e. NN0 z = ( ( k x. ( 2 ^ ( N + 2 ) ) ) + 1 ) ) ) -> ( ( N e. ( ZZ>= ` 2 ) /\ ( y x. z ) || ( FermatNo ` N ) ) -> E. k e. NN0 ( y x. z ) = ( ( k x. ( 2 ^ ( N + 2 ) ) ) + 1 ) ) ) )

  proof
    vy
    cv
    #
    c2
    cuz
    cfv
    #
    wcel
    #
    vz
    cv
    #
    @1
    wcel
    #
    wa
    #
    cN
    @1
    wcel
    #
    @0
    @3
    cmul
    co
    #
    cN
    cfmtno
    cfv
    #
    cdvds
    wbr
    #
    wa
    @6
    @0
    @8
    cdvds
    wbr
    #
    wa
    #
    @0
    vk
    cv
    #
    c2
    cN
    c2
    caddc
    co
    #
    cexp
    co
    #
    cmul
    co
    #
    c1
    caddc
    co
    #
    wceq
    #
    vk
    cn0
    wrex
    #
    wi
    #
    @6
    @3
    @8
    cdvds
    wbr
    #
    wa
    #
    @3
    @16
    wceq
    #
    vk
    cn0
    wrex
    #
    wi
    #
    wa
    #
    @7
    @16
    wceq
    #
    vk
    cn0
    wrex
    #
    @5
    @6
    @9
    @25
    @27
    wi
    #
    @5
    @6
    wa
    #
    @9
    @20
    @28
    @5
    @0
    cz
    wcel
    #
    @3
    cz
    wcel
    #
    @6
    @8
    cz
    wcel
    #
    @9
    @20
    wi
    @2
    @30
    @4
    c2
    @0
    eluzelz
    adantr
    #
    @4
    @31
    @2
    c2
    @3
    eluzelz
    adantl
    #
    @6
    cN
    cn0
    wcel
    #
    @32
    cN
    eluzge2nn0
    #
    @35
    @8
    cN
    fmtnonn
    nnzd
    syl
    #
    @0
    @3
    @8
    muldvds2
    syl2an3an
    @29
    @9
    @10
    @20
    @28
    wi
    @5
    @30
    @31
    @6
    @32
    @9
    @10
    wi
    @33
    @34
    @37
    @0
    @3
    @8
    muldvds1
    syl2an3an
    @29
    @10
    @20
    @28
    @29
    @10
    @20
    wa
    #
    wa
    @19
    @18
    @24
    @23
    @27
    @6
    @10
    @19
    @18
    wi
    @5
    @20
    @11
    @18
    pm2.27
    ad2ant2lr
    @6
    @20
    @24
    @23
    wi
    @5
    @10
    @21
    @23
    pm2.27
    ad2ant2l
    @29
    @18
    @23
    wa
    @27
    wi
    @38
    @29
    @18
    @23
    @27
    @18
    @0
    vm
    cv
    #
    @14
    cmul
    co
    #
    c1
    caddc
    co
    #
    wceq
    #
    vm
    cn0
    wrex
    @29
    @23
    @27
    wi
    #
    @17
    @42
    vk
    vm
    cn0
    vk
    vm
    weq
    #
    @16
    @41
    @0
    @44
    @15
    @40
    c1
    caddc
    @12
    @39
    @14
    cmul
    oveq1
    oveq1d
    eqeq2d
    cbvrexv
    @29
    @42
    @43
    vm
    cn0
    @29
    @39
    cn0
    wcel
    #
    wa
    #
    @23
    @42
    @27
    @23
    @3
    vn
    cv
    #
    @14
    cmul
    co
    #
    c1
    caddc
    co
    #
    wceq
    #
    vn
    cn0
    wrex
    @46
    @42
    @27
    wi
    #
    @22
    @50
    vk
    vn
    cn0
    vk
    vn
    weq
    #
    @16
    @49
    @3
    @52
    @15
    @48
    c1
    caddc
    @12
    @47
    @14
    cmul
    oveq1
    oveq1d
    eqeq2d
    cbvrexv
    @46
    @50
    @51
    vn
    cn0
    @29
    @45
    @47
    cn0
    wcel
    #
    @50
    @51
    wi
    @29
    @45
    @53
    wa
    #
    wa
    #
    @50
    @42
    @27
    @55
    @27
    @50
    @42
    wa
    #
    @41
    @49
    cmul
    co
    #
    @16
    wceq
    #
    vk
    cn0
    wrex
    #
    @6
    @54
    @59
    @5
    @6
    @54
    wa
    #
    @59
    @40
    @47
    cmul
    co
    #
    @39
    @47
    caddc
    co
    #
    caddc
    co
    #
    @14
    cmul
    co
    #
    c1
    caddc
    co
    #
    @16
    wceq
    #
    vk
    cn0
    wrex
    @60
    @66
    @65
    @65
    wceq
    #
    vk
    @63
    cn0
    @60
    @61
    @62
    @60
    @40
    @47
    @60
    @39
    @14
    @54
    @45
    @6
    @45
    @53
    simpl
    #
    adantl
    @6
    @14
    cn0
    wcel
    @54
    @6
    c2
    @13
    c2
    cn0
    wcel
    @6
    2nn0
    a1i
    #
    @6
    cN
    c2
    @36
    @69
    nn0addcld
    nn0expcld
    #
    adantr
    nn0mulcld
    @54
    @53
    @6
    @45
    @53
    simpr
    #
    adantl
    nn0mulcld
    @54
    @62
    cn0
    wcel
    @6
    @39
    @47
    nn0addcl
    #
    adantl
    nn0addcld
    @12
    @63
    wceq
    #
    @66
    @67
    wb
    @60
    @73
    @16
    @65
    @65
    @73
    @15
    @64
    c1
    caddc
    @12
    @63
    @14
    cmul
    oveq1
    oveq1d
    eqeq2d
    adantl
    @60
    @65
    eqidd
    rspcedvd
    @60
    @58
    @66
    vk
    cn0
    @60
    @12
    cn0
    wcel
    #
    wa
    #
    @57
    @65
    @16
    @75
    @57
    @40
    @48
    cmul
    co
    #
    @40
    @48
    caddc
    co
    #
    caddc
    co
    #
    c1
    caddc
    co
    #
    @65
    @75
    @40
    cc
    wcel
    #
    @48
    cc
    wcel
    #
    wa
    #
    @57
    @79
    wceq
    @60
    @82
    @74
    @60
    @80
    @81
    @60
    @39
    @14
    @54
    @39
    cc
    wcel
    #
    @6
    @45
    @83
    @53
    @39
    nn0cn
    adantr
    adantl
    @6
    @14
    cc
    wcel
    #
    @54
    @6
    @14
    @70
    nn0cnd
    adantr
    #
    mulcld
    #
    @60
    @47
    @14
    @54
    @47
    cc
    wcel
    #
    @6
    @54
    @47
    @71
    nn0cnd
    adantl
    #
    @85
    mulcld
    jca
    adantr
    @40
    @48
    muladd11r
    syl
    @75
    @78
    @64
    c1
    caddc
    @75
    @61
    @14
    cmul
    co
    #
    @77
    caddc
    co
    @89
    @62
    @14
    cmul
    co
    #
    caddc
    co
    #
    @78
    @64
    @75
    @77
    @90
    @89
    caddc
    @75
    @90
    @77
    @75
    @83
    @87
    @84
    w3a
    #
    @90
    @77
    wceq
    @60
    @92
    @74
    @60
    @83
    @87
    @84
    @54
    @83
    @6
    @54
    @39
    @68
    nn0cnd
    adantl
    @88
    @85
    3jca
    adantr
    @39
    @47
    @14
    adddir
    syl
    eqcomd
    oveq2d
    @75
    @76
    @89
    @77
    caddc
    @75
    @89
    @76
    @75
    @40
    @47
    @14
    @60
    @80
    @74
    @86
    adantr
    @60
    @87
    @74
    @88
    adantr
    @60
    @84
    @74
    @85
    adantr
    mulassd
    eqcomd
    oveq1d
    @75
    @61
    cc
    wcel
    #
    @62
    cc
    wcel
    #
    @84
    w3a
    #
    @64
    @91
    wceq
    @60
    @95
    @74
    @60
    @93
    @94
    @84
    @60
    @40
    @47
    @86
    @88
    mulcld
    @54
    @94
    @6
    @54
    @62
    @72
    nn0cnd
    adantl
    @85
    3jca
    adantr
    @61
    @62
    @14
    adddir
    syl
    3eqtr4d
    oveq1d
    eqtrd
    eqeq1d
    rexbidva
    mpbird
    adantll
    @56
    @26
    @58
    vk
    cn0
    @56
    @7
    @57
    @16
    @42
    @50
    @7
    @57
    wceq
    @0
    @41
    @3
    @49
    cmul
    oveq12
    ancoms
    eqeq1d
    rexbidv
    syl5ibrcom
    expd
    anassrs
    rexlimdva
    syl5bi
    com23
    rexlimdva
    syl5bi
    impd
    adantr
    syl2and
    exp32
    syld
    mpdd
    expimpd
    com23
end

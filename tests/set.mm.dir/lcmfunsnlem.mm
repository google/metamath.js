include "cfn.mm"
include "wcel.mm"
include "cz.mm"
include "wss.mm"
include "cv.mm"
include "cdvds.mm"
include "wbr.mm"
include "wral.mm"
include "clcmf.mm"
include "cfv.mm"
include "wi.mm"
include "csn.mm"
include "cun.mm"
include "clcm.mm"
include "co.mm"
include "wceq.mm"
include "wa.mm"
include "c0.mm"
include "sseq1.mm"
include "raleq.mm"
include "fveq2.mm"
include "breq1d.mm"
include "imbi12d.mm"
include "ralbidv.mm"
include "uneq1.mm"
include "fveq2d.mm"
include "oveq1d.mm"
include "eqeq12d.mm"
include "anbi12d.mm"
include "weq.mm"
include "c1.mm"
include "lcmf0.mm"
include "1dvds.mm"
include "syl5eqbr.mm"
include "a1d.mm"
include "adantl.mm"
include "ralrimiva.mm"
include "cabs.mm"
include "uncom.mm"
include "un0.mm"
include "eqtri.mm"
include "a1i.mm"
include "lcmfsn.mm"
include "1z.mm"
include "lcmcom.mm"
include "mpan.mm"
include "lcm1.mm"
include "3eqtrrd.mm"
include "3eqtrd.mm"
include "jca.mm"
include "unss.mm"
include "simpl.mm"
include "sylbir.mm"
include "vex.mm"
include "snss.mm"
include "w3a.mm"
include "lcmfunsnlem1.mm"
include "lcmfunsnlem2.mm"
include "3exp1.mm"
include "impcom.mm"
include "embantd.mm"
include "ex.mm"
include "com23.mm"
include "findcard2.mm"

theorem lcmfunsnlem
  let vk: setvar k
  let vm: setvar m
  let vn: setvar n
  let cY: class Y
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vl: setvar l
  let vi: setvar i

  disjoint k n
  disjoint k m
  disjoint m n
  disjoint Y k
  disjoint Y m
  disjoint Y n
  disjoint m x
  disjoint m y
  disjoint m z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint k x
  disjoint k y
  disjoint k z
  disjoint n x
  disjoint n y
  disjoint n z
  disjoint k l
  disjoint l m
  disjoint l y
  disjoint i k
  disjoint i l
  disjoint i m
  disjoint i n
  disjoint i y
  disjoint i z
  disjoint l n
  disjoint l z
  disjoint Y x
  disjoint Y y
  disjoint Y z
  assert |- ( ( Y C_ ZZ /\ Y e. Fin ) -> ( A. k e. ZZ ( A. m e. Y m || k -> ( _lcm ` Y ) || k ) /\ A. n e. ZZ ( _lcm ` ( Y u. { n } ) ) = ( ( _lcm ` Y ) lcm n ) ) )

  proof
    cY
    cfn
    wcel
    cY
    cz
    wss
    #
    vm
    cv
    vk
    cv
    #
    cdvds
    wbr
    #
    vm
    cY
    wral
    #
    cY
    clcmf
    cfv
    #
    @1
    cdvds
    wbr
    #
    wi
    #
    vk
    cz
    wral
    #
    cY
    vn
    cv
    #
    csn
    #
    cun
    #
    clcmf
    cfv
    #
    @4
    @8
    clcm
    co
    #
    wceq
    #
    vn
    cz
    wral
    #
    wa
    #
    vx
    cv
    #
    cz
    wss
    #
    @2
    vm
    @16
    wral
    #
    @16
    clcmf
    cfv
    #
    @1
    cdvds
    wbr
    #
    wi
    #
    vk
    cz
    wral
    #
    @16
    @9
    cun
    #
    clcmf
    cfv
    #
    @19
    @8
    clcm
    co
    #
    wceq
    #
    vn
    cz
    wral
    #
    wa
    #
    wi
    c0
    cz
    wss
    #
    @2
    vm
    c0
    wral
    #
    c0
    clcmf
    cfv
    #
    @1
    cdvds
    wbr
    #
    wi
    #
    vk
    cz
    wral
    #
    c0
    @9
    cun
    #
    clcmf
    cfv
    #
    @31
    @8
    clcm
    co
    #
    wceq
    #
    vn
    cz
    wral
    #
    wa
    #
    wi
    vy
    cv
    #
    cz
    wss
    #
    @2
    vm
    @41
    wral
    #
    @41
    clcmf
    cfv
    #
    @1
    cdvds
    wbr
    #
    wi
    #
    vk
    cz
    wral
    #
    @41
    @9
    cun
    #
    clcmf
    cfv
    #
    @44
    @8
    clcm
    co
    #
    wceq
    #
    vn
    cz
    wral
    #
    wa
    #
    wi
    #
    @41
    vz
    cv
    #
    csn
    #
    cun
    #
    cz
    wss
    #
    @2
    vm
    @57
    wral
    #
    @57
    clcmf
    cfv
    #
    @1
    cdvds
    wbr
    #
    wi
    #
    vk
    cz
    wral
    #
    @57
    @9
    cun
    #
    clcmf
    cfv
    #
    @60
    @8
    clcm
    co
    #
    wceq
    #
    vn
    cz
    wral
    #
    wa
    #
    wi
    @0
    @15
    wi
    vx
    vy
    vz
    cY
    @16
    c0
    wceq
    #
    @17
    @29
    @28
    @40
    @16
    c0
    cz
    sseq1
    @70
    @22
    @34
    @27
    @39
    @70
    @21
    @33
    vk
    cz
    @70
    @18
    @30
    @20
    @32
    @2
    vm
    @16
    c0
    raleq
    @70
    @19
    @31
    @1
    cdvds
    @16
    c0
    clcmf
    fveq2
    #
    breq1d
    imbi12d
    ralbidv
    @70
    @26
    @38
    vn
    cz
    @70
    @24
    @36
    @25
    @37
    @70
    @23
    @35
    clcmf
    @16
    c0
    @9
    uneq1
    fveq2d
    @70
    @19
    @31
    @8
    clcm
    @71
    oveq1d
    eqeq12d
    ralbidv
    anbi12d
    imbi12d
    vx
    vy
    weq
    #
    @17
    @42
    @28
    @53
    @16
    @41
    cz
    sseq1
    @72
    @22
    @47
    @27
    @52
    @72
    @21
    @46
    vk
    cz
    @72
    @18
    @43
    @20
    @45
    @2
    vm
    @16
    @41
    raleq
    @72
    @19
    @44
    @1
    cdvds
    @16
    @41
    clcmf
    fveq2
    #
    breq1d
    imbi12d
    ralbidv
    @72
    @26
    @51
    vn
    cz
    @72
    @24
    @49
    @25
    @50
    @72
    @23
    @48
    clcmf
    @16
    @41
    @9
    uneq1
    fveq2d
    @72
    @19
    @44
    @8
    clcm
    @73
    oveq1d
    eqeq12d
    ralbidv
    anbi12d
    imbi12d
    @16
    @57
    wceq
    #
    @17
    @58
    @28
    @69
    @16
    @57
    cz
    sseq1
    @74
    @22
    @63
    @27
    @68
    @74
    @21
    @62
    vk
    cz
    @74
    @18
    @59
    @20
    @61
    @2
    vm
    @16
    @57
    raleq
    @74
    @19
    @60
    @1
    cdvds
    @16
    @57
    clcmf
    fveq2
    #
    breq1d
    imbi12d
    ralbidv
    @74
    @26
    @67
    vn
    cz
    @74
    @24
    @65
    @25
    @66
    @74
    @23
    @64
    clcmf
    @16
    @57
    @9
    uneq1
    fveq2d
    @74
    @19
    @60
    @8
    clcm
    @75
    oveq1d
    eqeq12d
    ralbidv
    anbi12d
    imbi12d
    @16
    cY
    wceq
    #
    @17
    @0
    @28
    @15
    @16
    cY
    cz
    sseq1
    @76
    @22
    @7
    @27
    @14
    @76
    @21
    @6
    vk
    cz
    @76
    @18
    @3
    @20
    @5
    @2
    vm
    @16
    cY
    raleq
    @76
    @19
    @4
    @1
    cdvds
    @16
    cY
    clcmf
    fveq2
    #
    breq1d
    imbi12d
    ralbidv
    @76
    @26
    @13
    vn
    cz
    @76
    @24
    @11
    @25
    @12
    @76
    @23
    @10
    clcmf
    @16
    cY
    @9
    uneq1
    fveq2d
    @76
    @19
    @4
    @8
    clcm
    @77
    oveq1d
    eqeq12d
    ralbidv
    anbi12d
    imbi12d
    @29
    @34
    @39
    @29
    @33
    vk
    cz
    @1
    cz
    wcel
    #
    @33
    @29
    @78
    @32
    @30
    @78
    @31
    c1
    @1
    cdvds
    lcmf0
    @1
    1dvds
    syl5eqbr
    a1d
    adantl
    ralrimiva
    @29
    @38
    vn
    cz
    @8
    cz
    wcel
    #
    @38
    @29
    @79
    @36
    @9
    clcmf
    cfv
    @8
    cabs
    cfv
    #
    @37
    @79
    @35
    @9
    clcmf
    @35
    @9
    wceq
    @79
    @35
    @9
    c0
    cun
    @9
    c0
    @9
    uncom
    @9
    un0
    eqtri
    a1i
    fveq2d
    @8
    lcmfsn
    @79
    @37
    c1
    @8
    clcm
    co
    #
    @8
    c1
    clcm
    co
    #
    @80
    @79
    @31
    c1
    @8
    clcm
    @31
    c1
    wceq
    @79
    lcmf0
    a1i
    oveq1d
    c1
    cz
    wcel
    @79
    @81
    @82
    wceq
    1z
    c1
    @8
    lcmcom
    mpan
    @8
    lcm1
    3eqtrrd
    3eqtrd
    adantl
    ralrimiva
    jca
    @41
    cfn
    wcel
    #
    @58
    @54
    @69
    @83
    @58
    @54
    @69
    wi
    @83
    @58
    wa
    @42
    @53
    @69
    @58
    @42
    @83
    @58
    @42
    @56
    cz
    wss
    #
    wa
    #
    @42
    @41
    @56
    cz
    unss
    #
    @42
    @84
    simpl
    sylbir
    adantl
    @58
    @83
    @53
    @69
    wi
    #
    @58
    @85
    @83
    @87
    wi
    #
    @86
    @84
    @42
    @88
    @84
    @55
    cz
    wcel
    #
    @42
    @88
    wi
    @55
    cz
    vz
    vex
    snss
    @89
    @42
    @83
    @53
    @69
    @89
    @42
    @83
    w3a
    @53
    wa
    @63
    @68
    vy
    vz
    vk
    vm
    vn
    lcmfunsnlem1
    vy
    vz
    vk
    vm
    vn
    lcmfunsnlem2
    jca
    3exp1
    sylbir
    impcom
    sylbir
    impcom
    embantd
    ex
    com23
    findcard2
    impcom
end

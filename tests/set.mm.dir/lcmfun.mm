include "cz.mm"
include "wss.mm"
include "cfn.mm"
include "wcel.mm"
include "wa.mm"
include "cun.mm"
include "clcmf.mm"
include "cfv.mm"
include "clcm.mm"
include "co.mm"
include "wceq.mm"
include "wi.mm"
include "cv.mm"
include "c0.mm"
include "c1.mm"
include "csn.mm"
include "cleq1lem.mm"
include "uneq2.mm"
include "un0.mm"
include "syl6eq.mm"
include "fveq2d.mm"
include "fveq2.mm"
include "lcmf0.mm"
include "oveq2d.mm"
include "eqeq12d.mm"
include "imbi12d.mm"
include "weq.mm"
include "cabs.mm"
include "lcmfcl.mm"
include "nn0zd.mm"
include "lcm1.mm"
include "syl.mm"
include "cr.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "cn0.mm"
include "nn0re.mm"
include "nn0ge0.mm"
include "jca.mm"
include "absid.mm"
include "eqtrd.mm"
include "adantl.mm"
include "eqcomd.mm"
include "unass.mm"
include "eqcomi.mm"
include "a1i.mm"
include "simpl.mm"
include "unss.mm"
include "sylbir.mm"
include "adantr.mm"
include "unssd.mm"
include "unfi.mm"
include "ex.mm"
include "impcom.mm"
include "vex.mm"
include "snss.mm"
include "biimpri.mm"
include "lcmfunsn.mm"
include "syl3anc.mm"
include "anim1i.mm"
include "id.mm"
include "mpan9.mm"
include "oveq1d.mm"
include "anim2i.mm"
include "ancomd.mm"
include "lcmass.mm"
include "wb.mm"
include "w3a.mm"
include "simpr.mm"
include "3jca.mm"
include "eqeq2d.mm"
include "mpbird.mm"
include "exp31.mm"
include "com23.mm"
include "findcard2.mm"
include "expd.mm"

theorem lcmfun
  let cY: class Y
  let cZ: class Z
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( ( ( Y C_ ZZ /\ Y e. Fin ) /\ ( Z C_ ZZ /\ Z e. Fin ) ) -> ( _lcm ` ( Y u. Z ) ) = ( ( _lcm ` Y ) lcm ( _lcm ` Z ) ) )

  proof
    cZ
    cz
    wss
    #
    cZ
    cfn
    wcel
    #
    wa
    cY
    cz
    wss
    #
    cY
    cfn
    wcel
    #
    wa
    #
    cY
    cZ
    cun
    #
    clcmf
    cfv
    #
    cY
    clcmf
    cfv
    #
    cZ
    clcmf
    cfv
    #
    clcm
    co
    #
    wceq
    #
    @1
    @0
    @4
    @10
    wi
    @1
    @0
    @4
    @10
    vx
    cv
    #
    cz
    wss
    @4
    wa
    #
    cY
    @11
    cun
    #
    clcmf
    cfv
    #
    @7
    @11
    clcmf
    cfv
    #
    clcm
    co
    #
    wceq
    #
    wi
    c0
    cz
    wss
    #
    @4
    wa
    #
    @7
    @7
    c1
    clcm
    co
    #
    wceq
    #
    wi
    vy
    cv
    #
    cz
    wss
    #
    @4
    wa
    #
    cY
    @22
    cun
    #
    clcmf
    cfv
    #
    @7
    @22
    clcmf
    cfv
    #
    clcm
    co
    #
    wceq
    #
    wi
    #
    @22
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
    @4
    wa
    #
    cY
    @33
    cun
    #
    clcmf
    cfv
    #
    @7
    @33
    clcmf
    cfv
    #
    clcm
    co
    #
    wceq
    #
    wi
    @0
    @4
    wa
    #
    @10
    wi
    vx
    vy
    vz
    cZ
    @11
    c0
    wceq
    #
    @12
    @19
    @17
    @21
    @4
    @11
    c0
    cz
    cleq1lem
    @42
    @14
    @7
    @16
    @20
    @42
    @13
    cY
    clcmf
    @42
    @13
    cY
    c0
    cun
    cY
    @11
    c0
    cY
    uneq2
    cY
    un0
    syl6eq
    fveq2d
    @42
    @15
    c1
    @7
    clcm
    @42
    @15
    c0
    clcmf
    cfv
    c1
    @11
    c0
    clcmf
    fveq2
    lcmf0
    syl6eq
    oveq2d
    eqeq12d
    imbi12d
    vx
    vy
    weq
    #
    @12
    @24
    @17
    @29
    @4
    @11
    @22
    cz
    cleq1lem
    @43
    @14
    @26
    @16
    @28
    @43
    @13
    @25
    clcmf
    @11
    @22
    cY
    uneq2
    fveq2d
    @43
    @15
    @27
    @7
    clcm
    @11
    @22
    clcmf
    fveq2
    oveq2d
    eqeq12d
    imbi12d
    @11
    @33
    wceq
    #
    @12
    @35
    @17
    @40
    @4
    @11
    @33
    cz
    cleq1lem
    @44
    @14
    @37
    @16
    @39
    @44
    @13
    @36
    clcmf
    @11
    @33
    cY
    uneq2
    fveq2d
    @44
    @15
    @38
    @7
    clcm
    @11
    @33
    clcmf
    fveq2
    oveq2d
    eqeq12d
    imbi12d
    @11
    cZ
    wceq
    #
    @12
    @41
    @17
    @10
    @4
    @11
    cZ
    cz
    cleq1lem
    @45
    @14
    @6
    @16
    @9
    @45
    @13
    @5
    clcmf
    @11
    cZ
    cY
    uneq2
    fveq2d
    @45
    @15
    @8
    @7
    clcm
    @11
    cZ
    clcmf
    fveq2
    oveq2d
    eqeq12d
    imbi12d
    @19
    @20
    @7
    @4
    @20
    @7
    wceq
    @18
    @4
    @20
    @7
    cabs
    cfv
    #
    @7
    @4
    @7
    cz
    wcel
    #
    @20
    @46
    wceq
    @4
    @7
    cY
    lcmfcl
    #
    nn0zd
    #
    @7
    lcm1
    syl
    @4
    @7
    cr
    wcel
    #
    cc0
    @7
    cle
    wbr
    #
    wa
    #
    @46
    @7
    wceq
    @4
    @7
    cn0
    wcel
    #
    @52
    @48
    @53
    @50
    @51
    @7
    nn0re
    @7
    nn0ge0
    jca
    syl
    @7
    absid
    syl
    eqtrd
    adantl
    eqcomd
    @22
    cfn
    wcel
    #
    @35
    @30
    @40
    @54
    @35
    @30
    @40
    @54
    @35
    wa
    #
    @30
    wa
    #
    @40
    @37
    @7
    @27
    @31
    clcm
    co
    #
    clcm
    co
    #
    wceq
    #
    @56
    @37
    @26
    @31
    clcm
    co
    #
    @58
    @55
    @37
    @60
    wceq
    @30
    @55
    @37
    @25
    @32
    cun
    #
    clcmf
    cfv
    #
    @60
    @55
    @36
    @61
    clcmf
    @36
    @61
    wceq
    @55
    @61
    @36
    cY
    @22
    @32
    unass
    eqcomi
    a1i
    fveq2d
    @55
    @25
    cz
    wss
    #
    @25
    cfn
    wcel
    #
    @31
    cz
    wcel
    #
    @62
    @60
    wceq
    @35
    @63
    @54
    @35
    cY
    @22
    cz
    @4
    @2
    @34
    @2
    @3
    simpl
    adantl
    @34
    @23
    @4
    @34
    @23
    @32
    cz
    wss
    #
    wa
    #
    @23
    @22
    @32
    cz
    unss
    #
    @23
    @66
    simpl
    #
    sylbir
    #
    adantr
    #
    unssd
    adantl
    @35
    @54
    @64
    @4
    @54
    @64
    wi
    #
    @34
    @3
    @72
    @2
    @3
    @54
    @64
    cY
    @22
    unfi
    ex
    adantl
    adantl
    impcom
    @35
    @65
    @54
    @34
    @65
    @4
    @34
    @67
    @65
    @68
    @66
    @65
    @23
    @65
    @66
    @31
    cz
    vz
    vex
    snss
    biimpri
    adantl
    #
    sylbir
    adantr
    adantl
    #
    @31
    @25
    lcmfunsn
    syl3anc
    eqtrd
    adantr
    @56
    @60
    @28
    @31
    clcm
    co
    #
    @58
    @56
    @26
    @28
    @31
    clcm
    @55
    @24
    @30
    @29
    @35
    @24
    @54
    @34
    @23
    @4
    @70
    anim1i
    adantl
    @30
    id
    mpan9
    oveq1d
    @55
    @75
    @58
    wceq
    #
    @30
    @55
    @47
    @27
    cz
    wcel
    @65
    @76
    @35
    @47
    @54
    @4
    @47
    @34
    @49
    adantl
    adantl
    @55
    @27
    @55
    @23
    @54
    wa
    @27
    cn0
    wcel
    @55
    @54
    @23
    @35
    @23
    @54
    @71
    anim2i
    ancomd
    @22
    lcmfcl
    syl
    nn0zd
    @74
    @31
    @27
    @7
    lcmass
    syl3anc
    adantr
    eqtrd
    eqtrd
    @55
    @40
    @59
    wb
    @30
    @55
    @39
    @58
    @37
    @55
    @38
    @57
    @7
    clcm
    @55
    @23
    @54
    @65
    w3a
    #
    @38
    @57
    wceq
    @35
    @54
    @77
    @34
    @54
    @77
    wi
    #
    @4
    @34
    @67
    @78
    @68
    @67
    @54
    @77
    @67
    @54
    wa
    @23
    @54
    @65
    @67
    @23
    @54
    @69
    adantr
    @67
    @54
    simpr
    @67
    @65
    @54
    @73
    adantr
    3jca
    ex
    sylbir
    adantr
    impcom
    @31
    @22
    lcmfunsn
    syl
    oveq2d
    eqeq2d
    adantr
    mpbird
    exp31
    com23
    findcard2
    expd
    impcom
    impcom
end

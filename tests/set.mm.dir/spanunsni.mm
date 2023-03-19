include "csn.mm"
include "cspn.mm"
include "cfv.mm"
include "cph.mm"
include "co.mm"
include "cort.mm"
include "cpjh.mm"
include "cun.mm"
include "cv.mm"
include "wcel.mm"
include "cva.mm"
include "wceq.mm"
include "wrex.mm"
include "chshii.mm"
include "chil.mm"
include "wss.mm"
include "csh.mm"
include "snssi.mm"
include "spancl.mm"
include "mp2b.mm"
include "shseli.mm"
include "csm.mm"
include "cc.mm"
include "wi.mm"
include "elspansni.mm"
include "wa.mm"
include "pjclii.mm"
include "shmulcl.mm"
include "mp3an13.mm"
include "shaddcl.mm"
include "syl3an3.mm"
include "mp3an1.mm"
include "choccli.mm"
include "pjhclii.mm"
include "spansnmul.mm"
include "mpan.mm"
include "adantl.mm"
include "pjpji.mm"
include "oveq2i.mm"
include "ax-hvdistr1.mm"
include "mp3an23.mm"
include "syl5eq.mm"
include "oveq2d.mm"
include "cheli.mm"
include "hvmulcl.mm"
include "mpan2.mm"
include "jca.mm"
include "ax-hvass.mm"
include "3expb.mm"
include "syl2an.mm"
include "eqtr4d.mm"
include "rspceov.mm"
include "syl3anc.mm"
include "sylibr.mm"
include "oveq2.mm"
include "eqeq2d.mm"
include "biimpa.mm"
include "eleq1.mm"
include "biimparc.mm"
include "exp43.mm"
include "rexlimdv.mm"
include "syl5bi.mm"
include "rexlimiv.mm"
include "sylbi.mm"
include "cneg.mm"
include "negcl.mm"
include "syl.mm"
include "syl3an2.mm"
include "ancoms.mm"
include "c0v.mm"
include "c1.mm"
include "hvm1neg.mm"
include "hvnegid.mm"
include "sylancl.mm"
include "ax-hvcom.mm"
include "syl2anc.mm"
include "3eqtr3d.mm"
include "oveq1d.mm"
include "hvaddcl.mm"
include "hvaddid2.mm"
include "anim12i.mm"
include "hvadd4.mm"
include "impbii.mm"
include "eqriv.mm"
include "chssii.mm"
include "ax-mp.mm"
include "spanuni.mm"
include "spanid.mm"
include "oveq1i.mm"
include "eqtri.mm"
include "3eqtr4i.mm"

theorem spanunsni
  let cA: class A
  let cB: class B
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let vv: setvar v
  let vu: setvar u
  assume spanunsn.1: |- A e. CH
  assume spanunsn.2: |- B e. ~H


  assert |- ( span ` ( A u. { B } ) ) = ( span ` ( A u. { ( ( projh ` ( _|_ ` A ) ) ` B ) } ) )

  proof
    cA
    cB
    csn
    #
    cspn
    cfv
    #
    cph
    co
    #
    cA
    cB
    cA
    cort
    cfv
    #
    cpjh
    cfv
    cfv
    #
    csn
    #
    cspn
    cfv
    #
    cph
    co
    #
    cA
    @0
    cun
    cspn
    cfv
    #
    cA
    @5
    cun
    cspn
    cfv
    #
    vx
    @2
    @7
    vx
    cv
    #
    @2
    wcel
    #
    @10
    @7
    wcel
    #
    @11
    @10
    vy
    cv
    #
    vz
    cv
    #
    cva
    co
    #
    wceq
    #
    vz
    @1
    wrex
    #
    vy
    cA
    wrex
    @12
    vy
    vz
    cA
    @1
    @10
    cA
    spanunsn.1
    chshii
    #
    cB
    chil
    wcel
    #
    @0
    chil
    wss
    #
    @1
    csh
    wcel
    spanunsn.2
    cB
    chil
    snssi
    #
    @0
    spancl
    mp2b
    #
    shseli
    @17
    @12
    vy
    cA
    @13
    cA
    wcel
    #
    @16
    @12
    vz
    @1
    @14
    @1
    wcel
    @14
    vw
    cv
    #
    cB
    csm
    co
    #
    wceq
    #
    vw
    cc
    wrex
    @23
    @16
    @12
    wi
    #
    vw
    cB
    @14
    spanunsn.2
    elspansni
    @23
    @26
    @27
    vw
    cc
    @23
    @24
    cc
    wcel
    #
    @26
    @16
    @12
    @23
    @28
    wa
    #
    @13
    @25
    cva
    co
    #
    @7
    wcel
    #
    @10
    @30
    wceq
    #
    @12
    @26
    @16
    wa
    @29
    @30
    vv
    cv
    vu
    cv
    cva
    co
    #
    wceq
    vu
    @6
    wrex
    vv
    cA
    wrex
    #
    @31
    @29
    @13
    @24
    cB
    cA
    cpjh
    cfv
    cfv
    #
    csm
    co
    #
    cva
    co
    #
    cA
    wcel
    #
    @24
    @4
    csm
    co
    #
    @6
    wcel
    #
    @30
    @37
    @39
    cva
    co
    #
    wceq
    @34
    cA
    csh
    wcel
    #
    @23
    @28
    @38
    @18
    @28
    @42
    @23
    @36
    cA
    wcel
    #
    @38
    @42
    @28
    @35
    cA
    wcel
    #
    @43
    @18
    cB
    cA
    spanunsn.1
    spanunsn.2
    pjclii
    #
    @24
    @35
    cA
    shmulcl
    mp3an13
    @13
    @36
    cA
    shaddcl
    syl3an3
    mp3an1
    @28
    @40
    @23
    @4
    chil
    wcel
    #
    @28
    @40
    cB
    @3
    cA
    spanunsn.1
    choccli
    spanunsn.2
    pjhclii
    #
    @4
    @24
    spansnmul
    mpan
    adantl
    @29
    @30
    @13
    @36
    @39
    cva
    co
    #
    cva
    co
    #
    @41
    @29
    @25
    @48
    @13
    cva
    @28
    @25
    @48
    wceq
    @23
    @28
    @25
    @24
    @35
    @4
    cva
    co
    #
    csm
    co
    #
    @48
    cB
    @50
    @24
    csm
    cB
    cA
    spanunsn.1
    spanunsn.2
    pjpji
    oveq2i
    @28
    @35
    chil
    wcel
    #
    @46
    @51
    @48
    wceq
    cB
    cA
    spanunsn.1
    spanunsn.2
    pjhclii
    #
    @47
    @24
    @35
    @4
    ax-hvdistr1
    mp3an23
    syl5eq
    adantl
    #
    oveq2d
    @23
    @13
    chil
    wcel
    #
    @36
    chil
    wcel
    #
    @39
    chil
    wcel
    #
    wa
    @41
    @49
    wceq
    #
    @28
    @13
    cA
    spanunsn.1
    cheli
    #
    @28
    @56
    @57
    @28
    @52
    @56
    @53
    @24
    @35
    hvmulcl
    mpan2
    #
    @28
    @46
    @57
    @47
    @24
    @4
    hvmulcl
    mpan2
    #
    jca
    @55
    @56
    @57
    @58
    @13
    @36
    @39
    ax-hvass
    3expb
    syl2an
    eqtr4d
    vv
    vu
    cA
    @6
    @37
    @39
    @30
    cva
    rspceov
    syl3anc
    vv
    vu
    cA
    @6
    @30
    @18
    @46
    @5
    chil
    wss
    #
    @6
    csh
    wcel
    @47
    @4
    chil
    snssi
    #
    @5
    spancl
    mp2b
    #
    shseli
    sylibr
    @26
    @16
    @32
    @26
    @15
    @30
    @10
    @14
    @25
    @13
    cva
    oveq2
    eqeq2d
    biimpa
    @32
    @12
    @31
    @10
    @30
    @7
    eleq1
    biimparc
    syl2an
    exp43
    rexlimdv
    syl5bi
    rexlimdv
    rexlimiv
    sylbi
    @12
    @16
    vz
    @6
    wrex
    #
    vy
    cA
    wrex
    @11
    vy
    vz
    cA
    @6
    @10
    @18
    @64
    shseli
    @65
    @11
    vy
    cA
    @23
    @16
    @11
    vz
    @6
    @14
    @6
    wcel
    @14
    @39
    wceq
    #
    vw
    cc
    wrex
    @23
    @16
    @11
    wi
    #
    vw
    @4
    @14
    @47
    elspansni
    @23
    @66
    @67
    vw
    cc
    @23
    @28
    @66
    @16
    @11
    @29
    @13
    @39
    cva
    co
    #
    @2
    wcel
    #
    @10
    @68
    wceq
    #
    @11
    @66
    @16
    wa
    @29
    @68
    @33
    wceq
    vu
    @1
    wrex
    vv
    cA
    wrex
    #
    @69
    @29
    @24
    cneg
    #
    @35
    csm
    co
    #
    @13
    cva
    co
    #
    cA
    wcel
    #
    @25
    @1
    wcel
    #
    @68
    @74
    @25
    cva
    co
    #
    wceq
    @71
    @28
    @23
    @75
    @42
    @28
    @23
    @75
    @18
    @28
    @42
    @73
    cA
    wcel
    #
    @23
    @75
    @28
    @72
    cc
    wcel
    #
    @78
    @24
    negcl
    #
    @42
    @79
    @44
    @78
    @18
    @45
    @72
    @35
    cA
    shmulcl
    mp3an13
    syl
    @73
    @13
    cA
    shaddcl
    syl3an2
    mp3an1
    ancoms
    @28
    @76
    @23
    @19
    @28
    @76
    spanunsn.2
    cB
    @24
    spansnmul
    mpan
    adantl
    @29
    @68
    @74
    @48
    cva
    co
    #
    @77
    @29
    c0v
    @68
    cva
    co
    #
    @73
    @36
    cva
    co
    #
    @68
    cva
    co
    #
    @68
    @81
    @29
    c0v
    @83
    @68
    cva
    @28
    c0v
    @83
    wceq
    @23
    @28
    @36
    c1
    cneg
    @36
    csm
    co
    #
    cva
    co
    #
    @36
    @73
    cva
    co
    #
    c0v
    @83
    @28
    @85
    @73
    @36
    cva
    @28
    @52
    @85
    @73
    wceq
    @53
    @24
    @35
    hvm1neg
    mpan2
    oveq2d
    @28
    @56
    @86
    c0v
    wceq
    @60
    @36
    hvnegid
    syl
    @28
    @56
    @73
    chil
    wcel
    #
    @87
    @83
    wceq
    @60
    @28
    @79
    @52
    @88
    @80
    @53
    @72
    @35
    hvmulcl
    sylancl
    #
    @36
    @73
    ax-hvcom
    syl2anc
    3eqtr3d
    adantl
    oveq1d
    @29
    @68
    chil
    wcel
    #
    @82
    @68
    wceq
    @23
    @55
    @57
    @90
    @28
    @59
    @61
    @13
    @39
    hvaddcl
    syl2an
    @68
    hvaddid2
    syl
    @29
    @88
    @56
    wa
    #
    @55
    @57
    wa
    @84
    @81
    wceq
    @28
    @91
    @23
    @28
    @88
    @56
    @89
    @60
    jca
    adantl
    @23
    @55
    @28
    @57
    @59
    @61
    anim12i
    @73
    @36
    @13
    @39
    hvadd4
    syl2anc
    3eqtr3d
    @29
    @25
    @48
    @74
    cva
    @54
    oveq2d
    eqtr4d
    vv
    vu
    cA
    @1
    @74
    @25
    @68
    cva
    rspceov
    syl3anc
    vv
    vu
    cA
    @1
    @68
    @18
    @22
    shseli
    sylibr
    @66
    @16
    @70
    @66
    @15
    @68
    @10
    @14
    @39
    @13
    cva
    oveq2
    eqeq2d
    biimpa
    @70
    @11
    @69
    @10
    @68
    @2
    eleq1
    biimparc
    syl2an
    exp43
    rexlimdv
    syl5bi
    rexlimdv
    rexlimiv
    sylbi
    impbii
    eqriv
    @8
    cA
    cspn
    cfv
    #
    @1
    cph
    co
    @2
    cA
    @0
    cA
    spanunsn.1
    chssii
    #
    @19
    @20
    spanunsn.2
    @21
    ax-mp
    spanuni
    @92
    cA
    @1
    cph
    @42
    @92
    cA
    wceq
    @18
    cA
    spanid
    ax-mp
    #
    oveq1i
    eqtri
    @9
    @92
    @6
    cph
    co
    @7
    cA
    @5
    @93
    @46
    @62
    @47
    @63
    ax-mp
    spanuni
    @92
    cA
    @6
    cph
    @94
    oveq1i
    eqtri
    3eqtr4i
end

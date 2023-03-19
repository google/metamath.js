include "c1.mm"
include "cmin.mm"
include "co.mm"
include "cuz.mm"
include "cfv.mm"
include "cdvds.mm"
include "csn.mm"
include "cima.mm"
include "cv.mm"
include "cfz.mm"
include "cin.mm"
include "chash.mm"
include "cdiv.mm"
include "cmpt.mm"
include "cfl.mm"
include "cli.mm"
include "wcel.mm"
include "wa.mm"
include "cn.mm"
include "adantr.mm"
include "cz.mm"
include "simpr.mm"
include "hashnzfz.mm"
include "oveq1d.mm"
include "mpteq2dva.mm"
include "wbr.mm"
include "cc0.mm"
include "cvv.mm"
include "nnuz.mm"
include "1z.mm"
include "a1i.mm"
include "cxp.mm"
include "cc.mm"
include "nncnd.mm"
include "nnne0d.mm"
include "reccld.mm"
include "eqimss2i.mm"
include "nnex.mm"
include "climconst2.mm"
include "sylancl.mm"
include "mptex.mm"
include "ax-1cn.mm"
include "divcnv.mm"
include "mp1i.mm"
include "wceq.mm"
include "ovex.mm"
include "fvconst2.mm"
include "adantl.mm"
include "eqeltrd.mm"
include "cr.mm"
include "eqidd.mm"
include "oveq2.mm"
include "ovexd.mm"
include "fvmptd.mm"
include "nnrecred.mm"
include "recnd.mm"
include "oveq2d.mm"
include "oveq12d.mm"
include "eqtr4d.mm"
include "climsub.mm"
include "subid1d.mm"
include "breqtrd.mm"
include "nnre.mm"
include "wne.mm"
include "nnne0.mm"
include "rereccld.mm"
include "resubcld.mm"
include "oveq1.mm"
include "fveq2d.mm"
include "id.mm"
include "nndivred.mm"
include "reflcl.mm"
include "syl.mm"
include "redivcld.mm"
include "cle.mm"
include "clt.mm"
include "1cnd.mm"
include "nncn.mm"
include "divsubdird.mm"
include "cmul.mm"
include "divrecd.mm"
include "divcan3d.mm"
include "eqtrd.mm"
include "1red.mm"
include "crp.mm"
include "nnrp.mm"
include "caddc.mm"
include "readdcld.mm"
include "flle.mm"
include "wb.mm"
include "flflp1.mm"
include "syl2anc.mm"
include "mpbid.mm"
include "ltsub1dd.mm"
include "pncand.mm"
include "ltdiv1dd.mm"
include "eqbrtrrd.mm"
include "ltled.mm"
include "3brtr4d.mm"
include "lediv1dd.mm"
include "eqbrtrd.mm"
include "climsqz.mm"
include "zred.mm"
include "flcld.mm"
include "zcnd.mm"
include "divcld.mm"
include "3eqtr4d.mm"
include "cres.mm"
include "wss.mm"
include "uzssz.mm"
include "resmpt.mm"
include "ax-mp.mm"
include "breq1i.mm"
include "zsubcld.mm"
include "zex.mm"
include "climres.mm"
include "syl5bbr.mm"
include "reseq2i.mm"
include "nnssz.mm"
include "mp2an.mm"
include "3bitr3i.mm"
include "syl6bbr.mm"
include "mpbird.mm"

theorem hashnzfzclim
  let wph: wff ph
  let vk: setvar k
  let cJ: class J
  let cM: class M
  let vx: setvar x
  assume hashnzfzclim.m: |- ( ph -> M e. NN )
  assume hashnzfzclim.j: |- ( ph -> J e. ZZ )

  disjoint J k
  disjoint M k
  disjoint k ph
  disjoint k x
  disjoint J x
  disjoint M x
  disjoint ph x
  assert |- ( ph -> ( k e. ( ZZ>= ` ( J - 1 ) ) |-> ( ( # ` ( ( || " { M } ) i^i ( J ... k ) ) ) / k ) ) ~~> ( 1 / M ) )

  proof
    wph
    vk
    cJ
    c1
    cmin
    co
    #
    cuz
    cfv
    #
    cdvds
    cM
    csn
    cima
    cJ
    vk
    cv
    #
    cfz
    co
    cin
    chash
    cfv
    #
    @2
    cdiv
    co
    #
    cmpt
    vk
    @1
    @2
    cM
    cdiv
    co
    #
    cfl
    cfv
    #
    @0
    cM
    cdiv
    co
    #
    cfl
    cfv
    #
    cmin
    co
    #
    @2
    cdiv
    co
    #
    cmpt
    #
    c1
    cM
    cdiv
    co
    #
    cli
    wph
    vk
    @1
    @4
    @10
    wph
    @2
    @1
    wcel
    #
    wa
    #
    @3
    @9
    @2
    cdiv
    @14
    cJ
    @2
    cM
    wph
    cM
    cn
    wcel
    #
    @13
    hashnzfzclim.m
    adantr
    wph
    cJ
    cz
    wcel
    @13
    hashnzfzclim.j
    adantr
    wph
    @13
    simpr
    hashnzfz
    oveq1d
    mpteq2dva
    wph
    @11
    @12
    cli
    wbr
    #
    vk
    cn
    @10
    cmpt
    #
    @12
    cli
    wbr
    #
    wph
    @17
    @12
    cc0
    cmin
    co
    #
    @12
    cli
    wph
    @12
    cc0
    vx
    vk
    cn
    @6
    @2
    cdiv
    co
    #
    cmpt
    #
    vk
    cn
    @8
    @2
    cdiv
    co
    #
    cmpt
    #
    @17
    c1
    cvv
    cn
    nnuz
    c1
    cz
    wcel
    #
    wph
    1z
    a1i
    #
    wph
    @12
    vx
    vk
    cn
    @12
    c1
    @2
    cdiv
    co
    #
    cmin
    co
    #
    cmpt
    #
    @21
    c1
    cvv
    cn
    nnuz
    @25
    wph
    @28
    @19
    @12
    cli
    wph
    @12
    cc0
    vx
    cn
    @12
    csn
    cxp
    #
    vk
    cn
    @26
    cmpt
    #
    @28
    c1
    cvv
    cn
    nnuz
    @25
    wph
    @12
    cc
    wcel
    #
    @24
    @29
    @12
    cli
    wbr
    wph
    cM
    wph
    cM
    hashnzfzclim.m
    nncnd
    #
    wph
    cM
    hashnzfzclim.m
    nnne0d
    #
    reccld
    #
    1z
    @12
    c1
    cn
    cn
    c1
    cuz
    cfv
    #
    nnuz
    eqimss2i
    nnex
    climconst2
    sylancl
    @28
    cvv
    wcel
    wph
    vk
    cn
    @27
    nnex
    mptex
    a1i
    c1
    cc
    wcel
    @30
    cc0
    cli
    wbr
    wph
    ax-1cn
    c1
    vk
    divcnv
    mp1i
    wph
    vx
    cv
    #
    cn
    wcel
    #
    wa
    #
    @36
    @29
    cfv
    #
    @12
    cc
    @37
    @39
    @12
    wceq
    wph
    cn
    @12
    @36
    c1
    cM
    cdiv
    ovex
    fvconst2
    adantl
    #
    wph
    @31
    @37
    @34
    adantr
    #
    eqeltrd
    @38
    @36
    @30
    cfv
    #
    @38
    @42
    c1
    @36
    cdiv
    co
    #
    cr
    @38
    vk
    @36
    @26
    @43
    cn
    @30
    cvv
    @38
    @30
    eqidd
    @2
    @36
    wceq
    #
    @26
    @43
    wceq
    @38
    @2
    @36
    c1
    cdiv
    oveq2
    #
    adantl
    wph
    @37
    simpr
    #
    @38
    c1
    @36
    cdiv
    ovexd
    fvmptd
    #
    @38
    @36
    @46
    nnrecred
    eqeltrd
    recnd
    @38
    @36
    @28
    cfv
    #
    @12
    @43
    cmin
    co
    #
    @39
    @42
    cmin
    co
    @38
    vk
    @36
    @27
    @49
    cn
    @28
    cvv
    @38
    @28
    eqidd
    @44
    @27
    @49
    wceq
    @38
    @44
    @26
    @43
    @12
    cmin
    @45
    oveq2d
    adantl
    @46
    @38
    @12
    @43
    cmin
    ovexd
    fvmptd
    #
    @38
    @39
    @12
    @42
    @43
    cmin
    @40
    @47
    oveq12d
    eqtr4d
    climsub
    wph
    @12
    @34
    subid1d
    #
    breqtrd
    @21
    cvv
    wcel
    wph
    vk
    cn
    @20
    nnex
    mptex
    a1i
    @38
    @48
    @49
    cr
    @50
    @38
    @12
    @43
    wph
    @12
    cr
    wcel
    @37
    wph
    cM
    hashnzfzclim.m
    nnrecred
    adantr
    @38
    @36
    @37
    @36
    cr
    wcel
    wph
    @36
    nnre
    adantl
    #
    @37
    @36
    cc0
    wne
    wph
    @36
    nnne0
    adantl
    #
    rereccld
    resubcld
    #
    eqeltrd
    @38
    @36
    @21
    cfv
    #
    @36
    cM
    cdiv
    co
    #
    cfl
    cfv
    #
    @36
    cdiv
    co
    #
    cr
    @38
    vk
    @36
    @20
    @58
    cn
    @21
    cvv
    @38
    @21
    eqidd
    #
    @44
    @20
    @58
    wceq
    @38
    @44
    @6
    @57
    @2
    @36
    cdiv
    @44
    @5
    @56
    cfl
    @2
    @36
    cM
    cdiv
    oveq1
    fveq2d
    #
    @44
    id
    #
    oveq12d
    adantl
    @46
    @38
    @57
    @36
    cdiv
    ovexd
    #
    fvmptd
    #
    @38
    @57
    @36
    @38
    @56
    cr
    wcel
    #
    @57
    cr
    wcel
    @38
    @36
    cM
    @52
    wph
    @15
    @37
    hashnzfzclim.m
    adantr
    nndivred
    #
    @56
    reflcl
    syl
    #
    @52
    @53
    redivcld
    #
    eqeltrd
    #
    @38
    @49
    @58
    @48
    @55
    cle
    @38
    @49
    @58
    @54
    @67
    @38
    @56
    c1
    cmin
    co
    #
    @36
    cdiv
    co
    #
    @49
    @58
    clt
    @38
    @70
    @56
    @36
    cdiv
    co
    #
    @43
    cmin
    co
    @49
    @38
    @56
    c1
    @36
    @38
    @56
    @65
    recnd
    @38
    1cnd
    #
    @37
    @36
    cc
    wcel
    wph
    @36
    nncn
    adantl
    #
    @53
    divsubdird
    @38
    @71
    @12
    @43
    cmin
    @38
    @71
    @36
    @12
    cmul
    co
    #
    @36
    cdiv
    co
    @12
    @38
    @56
    @74
    @36
    cdiv
    @38
    @36
    cM
    @73
    wph
    cM
    cc
    wcel
    @37
    @32
    adantr
    wph
    cM
    cc0
    wne
    @37
    @33
    adantr
    divrecd
    oveq1d
    @38
    @12
    @36
    @41
    @73
    @53
    divcan3d
    eqtrd
    #
    oveq1d
    eqtrd
    @38
    @69
    @57
    @36
    @38
    @56
    c1
    @65
    @38
    1red
    #
    resubcld
    @66
    @37
    @36
    crp
    wcel
    wph
    @36
    nnrp
    adantl
    #
    @38
    @69
    @57
    c1
    caddc
    co
    #
    c1
    cmin
    co
    @57
    clt
    @38
    @56
    @78
    c1
    @65
    @38
    @57
    c1
    @66
    @76
    readdcld
    @76
    @38
    @57
    @56
    cle
    wbr
    #
    @56
    @78
    clt
    wbr
    #
    @38
    @64
    @79
    @65
    @56
    flle
    syl
    #
    @38
    @64
    @64
    @79
    @80
    wb
    @65
    @65
    @56
    @56
    flflp1
    syl2anc
    mpbid
    ltsub1dd
    @38
    @57
    c1
    @38
    @57
    @66
    recnd
    #
    @72
    pncand
    breqtrd
    ltdiv1dd
    eqbrtrrd
    ltled
    @50
    @38
    vk
    @36
    @20
    @58
    cn
    @21
    cvv
    @59
    @38
    @44
    wa
    #
    @6
    @57
    @2
    @36
    cdiv
    @83
    @5
    @56
    cfl
    @83
    @2
    @36
    cM
    cdiv
    @38
    @44
    simpr
    #
    oveq1d
    fveq2d
    @84
    oveq12d
    @46
    @62
    fvmptd
    #
    3brtr4d
    @38
    @55
    @58
    @12
    cle
    @85
    @38
    @58
    @71
    @12
    cle
    @38
    @57
    @56
    @36
    @66
    @65
    @77
    @81
    lediv1dd
    @75
    breqtrd
    eqbrtrd
    climsqz
    @17
    cvv
    wcel
    wph
    vk
    cn
    @10
    nnex
    mptex
    a1i
    wph
    @8
    cc
    wcel
    #
    @23
    cc0
    cli
    wbr
    wph
    @8
    wph
    @7
    wph
    @0
    cM
    wph
    cJ
    c1
    wph
    cJ
    hashnzfzclim.j
    zred
    wph
    1red
    resubcld
    hashnzfzclim.m
    nndivred
    flcld
    zcnd
    #
    @8
    vk
    divcnv
    syl
    @38
    @55
    @68
    recnd
    @38
    @36
    @23
    cfv
    #
    @8
    @36
    cdiv
    co
    #
    cc
    @38
    vk
    @36
    @22
    @89
    cn
    @23
    cvv
    @38
    @23
    eqidd
    @44
    @22
    @89
    wceq
    @38
    @2
    @36
    @8
    cdiv
    oveq2
    adantl
    @46
    @38
    @8
    @36
    cdiv
    ovexd
    fvmptd
    #
    @38
    @8
    @36
    wph
    @86
    @37
    @87
    adantr
    #
    @73
    @53
    divcld
    eqeltrd
    @38
    @57
    @8
    cmin
    co
    #
    @36
    cdiv
    co
    #
    @58
    @89
    cmin
    co
    @36
    @17
    cfv
    @55
    @88
    cmin
    co
    @38
    @57
    @8
    @36
    @82
    @91
    @73
    @53
    divsubdird
    @38
    vk
    @36
    @10
    @93
    cn
    @17
    cvv
    @38
    @17
    eqidd
    @44
    @10
    @93
    wceq
    @38
    @44
    @9
    @92
    @2
    @36
    cdiv
    @44
    @6
    @57
    @8
    cmin
    @60
    oveq1d
    @61
    oveq12d
    adantl
    @46
    @38
    @92
    @36
    cdiv
    ovexd
    fvmptd
    @38
    @55
    @58
    @88
    @89
    cmin
    @63
    @90
    oveq12d
    3eqtr4d
    climsub
    @51
    breqtrd
    wph
    @16
    vk
    cz
    @10
    cmpt
    #
    @12
    cli
    wbr
    #
    @18
    @16
    @94
    @1
    cres
    #
    @12
    cli
    wbr
    #
    wph
    @95
    @96
    @11
    @12
    cli
    @1
    cz
    wss
    @96
    @11
    wceq
    @0
    uzssz
    vk
    cz
    @1
    @10
    resmpt
    ax-mp
    breq1i
    wph
    @0
    cz
    wcel
    @94
    cvv
    wcel
    #
    @97
    @95
    wb
    wph
    cJ
    c1
    hashnzfzclim.j
    @25
    zsubcld
    vk
    cz
    @10
    zex
    mptex
    #
    @12
    @94
    @0
    cvv
    climres
    sylancl
    syl5bbr
    @94
    cn
    cres
    #
    @12
    cli
    wbr
    @94
    @35
    cres
    #
    @12
    cli
    wbr
    #
    @18
    @95
    @100
    @101
    @12
    cli
    cn
    @35
    @94
    nnuz
    reseq2i
    breq1i
    @100
    @17
    @12
    cli
    cn
    cz
    wss
    @100
    @17
    wceq
    nnssz
    vk
    cz
    cn
    @10
    resmpt
    ax-mp
    breq1i
    @24
    @98
    @102
    @95
    wb
    1z
    @99
    @12
    @94
    c1
    cvv
    climres
    mp2an
    3bitr3i
    syl6bbr
    mpbird
    eqbrtrd
end

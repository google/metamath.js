include "cv.mm"
include "cuz.mm"
include "cfv.mm"
include "wss.mm"
include "cc0.mm"
include "wne.mm"
include "cmul.mm"
include "cz.mm"
include "wcel.mm"
include "c1.mm"
include "cif.mm"
include "cmpt.mm"
include "cseq.mm"
include "cli.mm"
include "wbr.mm"
include "wa.mm"
include "wex.mm"
include "wrex.mm"
include "w3a.mm"
include "cfz.mm"
include "co.mm"
include "wf1o.mm"
include "cn.mm"
include "csb.mm"
include "wceq.mm"
include "wo.mm"
include "cio.mm"
include "cprod.mm"
include "3simpb.mm"
include "nfcv.mm"
include "nfv.mm"
include "nfcsb1v.mm"
include "nfif.mm"
include "weq.mm"
include "eleq1.mm"
include "csbeq1a.mm"
include "ifbieq1d.mm"
include "cbvmpt.mm"
include "cc.mm"
include "simpll.mm"
include "wral.mm"
include "ralrimiva.mm"
include "nfel1.mm"
include "eleq1d.mm"
include "rspc.mm"
include "syl5.mm"
include "mpan9.mm"
include "simplr.mm"
include "ad2antrr.mm"
include "simpr.mm"
include "syl6sseq.mm"
include "prodrb.mm"
include "biimpd.mm"
include "expimpd.mm"
include "rexlimdva.mm"
include "chash.mm"
include "clt.mm"
include "wiso.mm"
include "wor.mm"
include "cfn.mm"
include "cr.mm"
include "uzssz.mm"
include "zssre.mm"
include "sstri.mm"
include "eqsstri.mm"
include "syl6ss.mm"
include "ltso.mm"
include "soss.mm"
include "mpisyl.mm"
include "cen.mm"
include "fzfi.mm"
include "ovex.mm"
include "f1oen.mm"
include "adantl.mm"
include "ensymd.mm"
include "enfii.mm"
include "sylancr.mm"
include "fz1iso.mm"
include "syl2anc.mm"
include "fveq2.mm"
include "csbeq1d.mm"
include "csbco.mm"
include "syl6eqr.mm"
include "cbvmptv.mm"
include "eqid.mm"
include "simprl.mm"
include "simprr.mm"
include "prodmolem2a.mm"
include "expr.mm"
include "exlimdv.mm"
include "mpd.mm"
include "breq2.mm"
include "syl5ibrcom.mm"
include "jaod.mm"
include "adantr.mm"
include "wb.mm"
include "eleq2i.mm"
include "eluzelz.mm"
include "uztrn.mm"
include "ancoms.mm"
include "sseli.mm"
include "iftrue.mm"
include "eqeltrd.mm"
include "ex.mm"
include "wn.mm"
include "iffalse.mm"
include "ax-1cn.mm"
include "syl6eqel.mm"
include "pm2.61d1.mm"
include "fvmpt2.mm"
include "syl2anr.mm"
include "eqtr4d.mm"
include "sylan2br.mm"
include "nffvmpt1.mm"
include "nfeq2.mm"
include "eqeq12d.mm"
include "sylan2.mm"
include "anassrs.mm"
include "seqfeq.mm"
include "breq1d.mm"
include "anbi2d.mm"
include "exbidv.mm"
include "sylan2b.mm"
include "rexbidva.mm"
include "mpbid.mm"
include "sseq2d.mm"
include "rexeqdv.mm"
include "seqeq1.mm"
include "3anbi123d.mm"
include "rspcev.mm"
include "syl13anc.mm"
include "orcd.mm"
include "impbid.mm"
include "nfeq1.mm"
include "bitrd.mm"
include "iotabidv.mm"
include "df-prod.mm"
include "df-fv.mm"
include "3eqtr4g.mm"

theorem zprod
  let wph: wff ph
  let vy: setvar y
  let cA: class A
  let cB: class B
  let vk: setvar k
  let vn: setvar n
  let cF: class F
  let cM: class M
  let cZ: class Z
  let vf: setvar f
  let vg: setvar g
  let vi: setvar i
  let vj: setvar j
  let vm: setvar m
  let vx: setvar x
  let vz: setvar z
  assume zprod.1: |- Z = ( ZZ>= ` M )
  assume zprod.2: |- ( ph -> M e. ZZ )
  assume zprod.3: |- ( ph -> E. n e. Z E. y ( y =/= 0 /\ seq n ( x. , F ) ~~> y ) )
  assume zprod.4: |- ( ph -> A C_ Z )
  assume zprod.5: |- ( ( ph /\ k e. Z ) -> ( F ` k ) = if ( k e. A , B , 1 ) )
  assume zprod.6: |- ( ( ph /\ k e. A ) -> B e. CC )

  disjoint A k
  disjoint A n
  disjoint A y
  disjoint B n
  disjoint B y
  disjoint F k
  disjoint k n
  disjoint k ph
  disjoint k y
  disjoint M k
  disjoint M y
  disjoint n ph
  disjoint n y
  disjoint ph y
  disjoint Z n
  disjoint A f
  disjoint A g
  disjoint A i
  disjoint A j
  disjoint A m
  disjoint A x
  disjoint A z
  disjoint B f
  disjoint B g
  disjoint B i
  disjoint B j
  disjoint B m
  disjoint B x
  disjoint B z
  disjoint f g
  disjoint f i
  disjoint f j
  disjoint f k
  disjoint f m
  disjoint f n
  disjoint f ph
  disjoint f x
  disjoint F x
  disjoint f y
  disjoint F z
  disjoint g i
  disjoint g j
  disjoint g k
  disjoint g m
  disjoint g n
  disjoint g ph
  disjoint i j
  disjoint i k
  disjoint i m
  disjoint i n
  disjoint i ph
  disjoint j k
  disjoint j m
  disjoint j n
  disjoint j ph
  disjoint k m
  disjoint k x
  disjoint k z
  disjoint M f
  disjoint M g
  disjoint M i
  disjoint M j
  disjoint M m
  disjoint m n
  disjoint m ph
  disjoint m x
  disjoint M x
  disjoint m y
  disjoint M z
  disjoint n x
  disjoint n z
  disjoint ph x
  disjoint ph z
  disjoint x y
  disjoint Z m
  assert |- ( ph -> prod_ k e. A B = ( ~~> ` seq M ( x. , F ) ) )

  proof
    wph
    cA
    vm
    cv
    #
    cuz
    cfv
    #
    wss
    #
    vy
    cv
    #
    cc0
    wne
    #
    cmul
    vk
    cz
    vk
    cv
    #
    cA
    wcel
    #
    cB
    c1
    cif
    #
    cmpt
    #
    vn
    cv
    #
    cseq
    #
    @3
    cli
    wbr
    #
    wa
    #
    vy
    wex
    #
    vn
    @1
    wrex
    #
    cmul
    @8
    @0
    cseq
    #
    vx
    cv
    #
    cli
    wbr
    #
    w3a
    #
    vm
    cz
    wrex
    #
    c1
    @0
    cfz
    co
    #
    cA
    vf
    cv
    #
    wf1o
    #
    @16
    @0
    cmul
    vn
    cn
    vk
    @9
    @21
    cfv
    #
    cB
    csb
    #
    cmpt
    #
    c1
    cseq
    cfv
    #
    wceq
    #
    wa
    #
    vf
    wex
    #
    vm
    cn
    wrex
    #
    wo
    #
    vx
    cio
    cmul
    cF
    cM
    cseq
    #
    @16
    cli
    wbr
    #
    vx
    cio
    cA
    cB
    vk
    cprod
    @32
    cli
    cfv
    wph
    @31
    @33
    vx
    wph
    @31
    cmul
    @8
    cM
    cseq
    #
    @16
    cli
    wbr
    #
    @33
    wph
    @31
    @35
    wph
    @19
    @35
    @30
    wph
    @18
    @35
    vm
    cz
    @18
    @2
    @17
    wa
    wph
    @0
    cz
    wcel
    #
    wa
    #
    @35
    @2
    @14
    @17
    3simpb
    @37
    @2
    @17
    @35
    @37
    @2
    wa
    #
    @17
    @35
    @38
    cA
    vk
    vi
    cv
    #
    cB
    csb
    #
    @16
    vi
    @8
    @0
    cM
    vk
    vi
    cz
    @7
    @39
    cA
    wcel
    #
    @40
    c1
    cif
    vi
    @7
    nfcv
    @41
    vk
    @40
    c1
    @41
    vk
    nfv
    vk
    @39
    cB
    nfcsb1v
    #
    vk
    c1
    nfcv
    nfif
    vk
    vi
    weq
    #
    @6
    @41
    cB
    @40
    c1
    @5
    @39
    cA
    eleq1
    vk
    @39
    cB
    csbeq1a
    #
    ifbieq1d
    cbvmpt
    #
    @38
    wph
    @41
    @40
    cc
    wcel
    #
    wph
    @36
    @2
    simpll
    wph
    cB
    cc
    wcel
    #
    vk
    cA
    wral
    @41
    @46
    wph
    @47
    vk
    cA
    zprod.6
    ralrimiva
    @47
    @46
    vk
    @39
    cA
    vk
    @40
    cc
    @42
    nfel1
    @43
    cB
    @40
    cc
    @44
    eleq1d
    rspc
    syl5
    #
    mpan9
    wph
    @36
    @2
    simplr
    wph
    cM
    cz
    wcel
    #
    @36
    @2
    zprod.2
    ad2antrr
    @37
    @2
    simpr
    wph
    cA
    cM
    cuz
    cfv
    #
    wss
    #
    @36
    @2
    wph
    cA
    cZ
    @50
    zprod.4
    zprod.1
    syl6sseq
    #
    ad2antrr
    prodrb
    biimpd
    expimpd
    syl5
    rexlimdva
    wph
    @29
    @35
    vm
    cn
    wph
    @0
    cn
    wcel
    #
    wa
    #
    @28
    @35
    vf
    @54
    @22
    @27
    @35
    @54
    @22
    wa
    #
    @35
    @27
    @34
    @26
    cli
    wbr
    #
    @55
    c1
    cA
    chash
    cfv
    cfz
    co
    cA
    clt
    clt
    vg
    cv
    #
    wiso
    #
    vg
    wex
    #
    @56
    @55
    cA
    clt
    wor
    #
    cA
    cfn
    wcel
    #
    @59
    @55
    cA
    cr
    wss
    #
    cr
    clt
    wor
    @60
    wph
    @62
    @53
    @22
    wph
    cA
    cZ
    cr
    zprod.4
    cZ
    @50
    cr
    zprod.1
    @50
    cz
    cr
    cM
    uzssz
    #
    zssre
    sstri
    eqsstri
    syl6ss
    ad2antrr
    ltso
    cA
    cr
    clt
    soss
    mpisyl
    @55
    @20
    cfn
    wcel
    cA
    @20
    cen
    wbr
    @61
    c1
    @0
    fzfi
    @55
    @20
    cA
    @22
    @20
    cA
    cen
    wbr
    @54
    @20
    cA
    @21
    c1
    @0
    cfz
    ovex
    f1oen
    adantl
    ensymd
    cA
    @20
    enfii
    sylancr
    cA
    clt
    vg
    fz1iso
    syl2anc
    @55
    @58
    @56
    vg
    @54
    @22
    @58
    @56
    @54
    @22
    @58
    wa
    #
    wa
    #
    cA
    @40
    vf
    vj
    vi
    @8
    @25
    vj
    cn
    vi
    vj
    cv
    #
    @57
    cfv
    @40
    csb
    cmpt
    #
    @57
    cM
    @0
    @45
    @65
    wph
    @41
    @46
    wph
    @53
    @64
    simpll
    @48
    mpan9
    vn
    vj
    cn
    @24
    vi
    @66
    @21
    cfv
    #
    @40
    csb
    #
    vn
    vj
    weq
    #
    @24
    vk
    @68
    cB
    csb
    @69
    @70
    vk
    @23
    @68
    cB
    @9
    @66
    @21
    fveq2
    csbeq1d
    vk
    vi
    @68
    cB
    csbco
    syl6eqr
    cbvmptv
    @67
    eqid
    wph
    @53
    @64
    simplr
    wph
    @49
    @53
    @64
    zprod.2
    ad2antrr
    wph
    @51
    @53
    @64
    @52
    ad2antrr
    @54
    @22
    @58
    simprl
    @54
    @22
    @58
    simprr
    prodmolem2a
    expr
    exlimdv
    mpd
    @16
    @26
    @34
    cli
    breq2
    syl5ibrcom
    expimpd
    exlimdv
    rexlimdva
    jaod
    wph
    @35
    @31
    wph
    @35
    wa
    #
    @19
    @30
    @71
    @49
    cA
    cZ
    wss
    #
    @13
    vn
    cZ
    wrex
    #
    @35
    @19
    wph
    @49
    @35
    zprod.2
    adantr
    wph
    @72
    @35
    zprod.4
    adantr
    wph
    @73
    @35
    wph
    @4
    cmul
    cF
    @9
    cseq
    #
    @3
    cli
    wbr
    #
    wa
    #
    vy
    wex
    #
    vn
    cZ
    wrex
    @73
    zprod.3
    wph
    @77
    @13
    vn
    cZ
    @9
    cZ
    wcel
    wph
    @9
    @50
    wcel
    #
    @77
    @13
    wb
    cZ
    @50
    @9
    zprod.1
    eleq2i
    wph
    @78
    wa
    #
    @76
    @12
    vy
    @79
    @75
    @11
    @4
    @79
    @74
    @10
    @3
    cli
    @79
    cmul
    vz
    cF
    @8
    @9
    @78
    @9
    cz
    wcel
    wph
    cM
    @9
    eluzelz
    adantl
    wph
    @78
    vz
    cv
    #
    @9
    cuz
    cfv
    wcel
    #
    @80
    cF
    cfv
    #
    @80
    @8
    cfv
    #
    wceq
    #
    @78
    @81
    wa
    wph
    @80
    @50
    wcel
    #
    @84
    @81
    @78
    @85
    @9
    @80
    cM
    uztrn
    ancoms
    wph
    @5
    cF
    cfv
    #
    @5
    @8
    cfv
    #
    wceq
    #
    vk
    @50
    wral
    @85
    @84
    wph
    @88
    vk
    @50
    @5
    @50
    wcel
    #
    wph
    @5
    cZ
    wcel
    #
    @88
    cZ
    @50
    @5
    zprod.1
    eleq2i
    #
    wph
    @90
    wa
    #
    @86
    @7
    @87
    zprod.5
    @90
    @5
    cz
    wcel
    @7
    cc
    wcel
    #
    @87
    @7
    wceq
    wph
    cZ
    cz
    @5
    cZ
    @50
    cz
    zprod.1
    @63
    eqsstri
    sseli
    wph
    @6
    @93
    wph
    @6
    @93
    wph
    @6
    wa
    @7
    cB
    cc
    @6
    @7
    cB
    wceq
    wph
    @6
    cB
    c1
    iftrue
    adantl
    zprod.6
    eqeltrd
    ex
    @6
    wn
    @7
    c1
    cc
    @6
    cB
    c1
    iffalse
    ax-1cn
    syl6eqel
    pm2.61d1
    vk
    cz
    @7
    cc
    @8
    @8
    eqid
    fvmpt2
    syl2anr
    #
    eqtr4d
    sylan2br
    ralrimiva
    @88
    @84
    vk
    @80
    @50
    vk
    @82
    @83
    vk
    cz
    @7
    @80
    nffvmpt1
    #
    nfeq2
    vk
    vz
    weq
    #
    @86
    @82
    @87
    @83
    @5
    @80
    cF
    fveq2
    #
    @5
    @80
    @8
    fveq2
    #
    eqeq12d
    rspc
    mpan9
    sylan2
    anassrs
    seqfeq
    breq1d
    anbi2d
    exbidv
    sylan2b
    rexbidva
    mpbid
    adantr
    wph
    @35
    simpr
    @18
    @72
    @73
    @35
    w3a
    vm
    cM
    cz
    @0
    cM
    wceq
    #
    @2
    @72
    @14
    @73
    @17
    @35
    @99
    @1
    cZ
    cA
    @99
    @1
    @50
    cZ
    @0
    cM
    cuz
    fveq2
    zprod.1
    syl6eqr
    #
    sseq2d
    @99
    @13
    vn
    @1
    cZ
    @100
    rexeqdv
    @99
    @15
    @34
    @16
    cli
    cmul
    @8
    @0
    cM
    seqeq1
    breq1d
    3anbi123d
    rspcev
    syl13anc
    orcd
    ex
    impbid
    wph
    @34
    @32
    @16
    cli
    wph
    cmul
    vz
    @8
    cF
    cM
    zprod.2
    wph
    @87
    @86
    wceq
    #
    vk
    @50
    wral
    @85
    @83
    @82
    wceq
    #
    wph
    @101
    vk
    @50
    @89
    wph
    @90
    @101
    @91
    @92
    @87
    @7
    @86
    @94
    zprod.5
    eqtr4d
    sylan2br
    ralrimiva
    @101
    @102
    vk
    @80
    @50
    vk
    @83
    @82
    @95
    nfeq1
    @96
    @87
    @83
    @86
    @82
    @98
    @97
    eqeq12d
    rspc
    mpan9
    seqfeq
    breq1d
    bitrd
    iotabidv
    vx
    vy
    cA
    cB
    vf
    vk
    vm
    vn
    df-prod
    vx
    @32
    cli
    df-fv
    3eqtr4g
end

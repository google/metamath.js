include "cv.mm"
include "cuz.mm"
include "cfv.mm"
include "wss.mm"
include "caddc.mm"
include "cz.mm"
include "wcel.mm"
include "csb.mm"
include "cc0.mm"
include "cif.mm"
include "cmpt.mm"
include "cseq.mm"
include "cli.mm"
include "wbr.mm"
include "wa.mm"
include "wrex.mm"
include "c1.mm"
include "cfz.mm"
include "co.mm"
include "wf1o.mm"
include "cn.mm"
include "wceq.mm"
include "wex.mm"
include "wo.mm"
include "cio.mm"
include "csu.mm"
include "eleq1.mm"
include "csbeq1.mm"
include "ifbieq1d.mm"
include "cbvmptv.mm"
include "cc.mm"
include "simpll.mm"
include "wral.mm"
include "ralrimiva.mm"
include "nfcsb1v.mm"
include "nfel1.mm"
include "csbeq1a.mm"
include "eleq1d.mm"
include "rspc.mm"
include "syl5.mm"
include "mpan9.mm"
include "simplr.mm"
include "ad2antrr.mm"
include "simpr.mm"
include "syl6sseq.mm"
include "sumrb.mm"
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
include "eqsstri.mm"
include "zssre.mm"
include "sstri.mm"
include "ltso.mm"
include "soss.mm"
include "mp2.mm"
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
include "eqid.mm"
include "simprl.mm"
include "simprr.mm"
include "summolem2a.mm"
include "expr.mm"
include "exlimdv.mm"
include "mpd.mm"
include "breq2.mm"
include "syl5ibrcom.mm"
include "jaod.mm"
include "adantr.mm"
include "sseq2d.mm"
include "seqeq1.mm"
include "breq1d.mm"
include "anbi12d.mm"
include "rspcev.mm"
include "syl12anc.mm"
include "orcd.mm"
include "ex.mm"
include "impbid.mm"
include "cvv.mm"
include "sseldi.mm"
include "syl6eleqr.mm"
include "nfeq2.mm"
include "eqeq12d.mm"
include "sylc.mm"
include "fvex.mm"
include "syl6eqelr.mm"
include "nfcv.mm"
include "nfv.mm"
include "nfif.mm"
include "cbvmpt.mm"
include "eqcomi.mm"
include "fvmpts.mm"
include "eqtr4d.mm"
include "seqfeq.mm"
include "bitrd.mm"
include "iotabidv.mm"
include "df-sum.mm"
include "df-fv.mm"
include "3eqtr4g.mm"

theorem zsum
  let wph: wff ph
  let cA: class A
  let cB: class B
  let vk: setvar k
  let cF: class F
  let cM: class M
  let cZ: class Z
  let vf: setvar f
  let vg: setvar g
  let vi: setvar i
  let vj: setvar j
  let vm: setvar m
  let vn: setvar n
  let vx: setvar x
  assume zsum.1: |- Z = ( ZZ>= ` M )
  assume zsum.2: |- ( ph -> M e. ZZ )
  assume zsum.3: |- ( ph -> A C_ Z )
  assume zsum.4: |- ( ( ph /\ k e. Z ) -> ( F ` k ) = if ( k e. A , B , 0 ) )
  assume zsum.5: |- ( ( ph /\ k e. A ) -> B e. CC )

  disjoint A k
  disjoint F k
  disjoint k ph
  disjoint Z k
  disjoint M k
  disjoint f g
  disjoint f i
  disjoint f j
  disjoint f k
  disjoint f m
  disjoint f n
  disjoint f x
  disjoint A f
  disjoint g i
  disjoint g j
  disjoint g k
  disjoint g m
  disjoint g n
  disjoint g x
  disjoint A g
  disjoint i j
  disjoint i k
  disjoint i m
  disjoint i n
  disjoint i x
  disjoint A i
  disjoint j k
  disjoint j m
  disjoint j n
  disjoint j x
  disjoint A j
  disjoint k m
  disjoint k n
  disjoint k x
  disjoint m n
  disjoint m x
  disjoint A m
  disjoint n x
  disjoint A n
  disjoint A x
  disjoint F j
  disjoint F n
  disjoint F x
  disjoint f ph
  disjoint g ph
  disjoint i ph
  disjoint j ph
  disjoint m ph
  disjoint ph x
  disjoint B f
  disjoint B g
  disjoint B i
  disjoint B j
  disjoint B m
  disjoint B n
  disjoint B x
  disjoint M f
  disjoint M g
  disjoint M i
  disjoint M j
  disjoint M m
  disjoint M x
  assert |- ( ph -> sum_ k e. A B = ( ~~> ` seq M ( + , F ) ) )

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
    caddc
    vn
    cz
    vn
    cv
    #
    cA
    wcel
    #
    vk
    @3
    cB
    csb
    #
    cc0
    cif
    #
    cmpt
    #
    @0
    cseq
    #
    vx
    cv
    #
    cli
    wbr
    #
    wa
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
    @9
    @0
    caddc
    vn
    cn
    vk
    @3
    @14
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
    caddc
    cF
    cM
    cseq
    #
    @9
    cli
    wbr
    #
    vx
    cio
    cA
    cB
    vk
    csu
    @25
    cli
    cfv
    wph
    @24
    @26
    vx
    wph
    @24
    caddc
    @7
    cM
    cseq
    #
    @9
    cli
    wbr
    #
    @26
    wph
    @24
    @28
    wph
    @12
    @28
    @23
    wph
    @11
    @28
    vm
    cz
    wph
    @0
    cz
    wcel
    #
    wa
    #
    @2
    @10
    @28
    @30
    @2
    wa
    #
    @10
    @28
    @31
    cA
    vk
    vi
    cv
    #
    cB
    csb
    #
    @9
    vi
    @7
    @0
    cM
    vn
    vi
    cz
    @6
    @32
    cA
    wcel
    #
    @33
    cc0
    cif
    @3
    @32
    wceq
    @4
    @34
    @5
    @33
    cc0
    @3
    @32
    cA
    eleq1
    vk
    @3
    @32
    cB
    csbeq1
    ifbieq1d
    cbvmptv
    #
    @31
    wph
    @34
    @33
    cc
    wcel
    #
    wph
    @29
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
    @34
    @36
    wph
    @37
    vk
    cA
    zsum.5
    ralrimiva
    @37
    @36
    vk
    @32
    cA
    vk
    @33
    cc
    vk
    @32
    cB
    nfcsb1v
    nfel1
    vk
    cv
    #
    @32
    wceq
    cB
    @33
    cc
    vk
    @32
    cB
    csbeq1a
    eleq1d
    rspc
    syl5
    #
    mpan9
    wph
    @29
    @2
    simplr
    wph
    cM
    cz
    wcel
    #
    @29
    @2
    zsum.2
    ad2antrr
    @30
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
    @29
    @2
    wph
    cA
    cZ
    @41
    zsum.3
    zsum.1
    syl6sseq
    #
    ad2antrr
    sumrb
    biimpd
    expimpd
    rexlimdva
    wph
    @22
    @28
    vm
    cn
    wph
    @0
    cn
    wcel
    #
    wa
    #
    @21
    @28
    vf
    @45
    @15
    @20
    @28
    @45
    @15
    wa
    #
    @28
    @20
    @27
    @19
    cli
    wbr
    #
    @46
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
    @47
    @46
    cA
    clt
    wor
    #
    cA
    cfn
    wcel
    #
    @50
    @46
    cA
    cZ
    wss
    #
    cZ
    clt
    wor
    #
    @51
    wph
    @53
    @44
    @15
    zsum.3
    ad2antrr
    cZ
    cr
    wss
    cr
    clt
    wor
    @54
    cZ
    cz
    cr
    cZ
    @41
    cz
    zsum.1
    cM
    uzssz
    #
    eqsstri
    zssre
    sstri
    ltso
    cZ
    cr
    clt
    soss
    mp2
    cA
    cZ
    clt
    soss
    mpisyl
    @46
    @13
    cfn
    wcel
    cA
    @13
    cen
    wbr
    @52
    c1
    @0
    fzfi
    @46
    @13
    cA
    @15
    @13
    cA
    cen
    wbr
    @45
    @13
    cA
    @14
    c1
    @0
    cfz
    ovex
    f1oen
    adantl
    ensymd
    cA
    @13
    enfii
    sylancr
    cA
    clt
    vg
    fz1iso
    syl2anc
    @46
    @49
    @47
    vg
    @45
    @15
    @49
    @47
    @45
    @15
    @49
    wa
    #
    wa
    #
    cA
    @33
    vf
    vi
    vj
    @7
    @18
    vj
    cn
    vi
    vj
    cv
    #
    @48
    cfv
    @33
    csb
    cmpt
    #
    @48
    cM
    @0
    @35
    @57
    wph
    @34
    @36
    wph
    @44
    @56
    simpll
    @39
    mpan9
    vn
    vj
    cn
    @17
    vi
    @58
    @14
    cfv
    #
    @33
    csb
    #
    @3
    @58
    wceq
    #
    @17
    vk
    @60
    cB
    csb
    @61
    @62
    vk
    @16
    @60
    cB
    @3
    @58
    @14
    fveq2
    csbeq1d
    vk
    vi
    @60
    cB
    csbco
    syl6eqr
    cbvmptv
    @59
    eqid
    wph
    @44
    @56
    simplr
    wph
    @40
    @44
    @56
    zsum.2
    ad2antrr
    wph
    @42
    @44
    @56
    @43
    ad2antrr
    @45
    @15
    @49
    simprl
    @45
    @15
    @49
    simprr
    summolem2a
    expr
    exlimdv
    mpd
    @9
    @19
    @27
    cli
    breq2
    syl5ibrcom
    expimpd
    exlimdv
    rexlimdva
    jaod
    wph
    @28
    @24
    wph
    @28
    wa
    #
    @12
    @23
    @63
    @40
    @42
    @28
    @12
    wph
    @40
    @28
    zsum.2
    adantr
    wph
    @42
    @28
    @43
    adantr
    wph
    @28
    simpr
    @11
    @42
    @28
    wa
    vm
    cM
    cz
    @0
    cM
    wceq
    #
    @2
    @42
    @10
    @28
    @64
    @1
    @41
    cA
    @0
    cM
    cuz
    fveq2
    sseq2d
    @64
    @8
    @27
    @9
    cli
    caddc
    @7
    @0
    cM
    seqeq1
    breq1d
    anbi12d
    rspcev
    syl12anc
    orcd
    ex
    impbid
    wph
    @27
    @25
    @9
    cli
    wph
    caddc
    vj
    @7
    cF
    cM
    zsum.2
    wph
    @58
    @41
    wcel
    #
    wa
    #
    @58
    @7
    cfv
    #
    vk
    @58
    @38
    cA
    wcel
    #
    cB
    cc0
    cif
    #
    csb
    #
    @58
    cF
    cfv
    #
    @66
    @58
    cz
    wcel
    @70
    cvv
    wcel
    @67
    @70
    wceq
    @66
    @41
    cz
    @58
    @55
    wph
    @65
    simpr
    #
    sseldi
    @66
    @70
    @71
    cvv
    @66
    @58
    cZ
    wcel
    @38
    cF
    cfv
    #
    @69
    wceq
    #
    vk
    cZ
    wral
    #
    @71
    @70
    wceq
    #
    @66
    @58
    @41
    cZ
    @72
    zsum.1
    syl6eleqr
    wph
    @75
    @65
    wph
    @74
    vk
    cZ
    zsum.4
    ralrimiva
    adantr
    @74
    @76
    vk
    @58
    cZ
    vk
    @71
    @70
    vk
    @58
    @69
    nfcsb1v
    nfeq2
    @38
    @58
    wceq
    @73
    @71
    @69
    @70
    @38
    @58
    cF
    fveq2
    vk
    @58
    @69
    csbeq1a
    eqeq12d
    rspc
    sylc
    #
    @58
    cF
    fvex
    syl6eqelr
    vk
    @58
    @69
    cz
    @7
    cvv
    vk
    cz
    @69
    cmpt
    @7
    vk
    vn
    cz
    @69
    @6
    vn
    @69
    nfcv
    @4
    vk
    @5
    cc0
    @4
    vk
    nfv
    vk
    @3
    cB
    nfcsb1v
    vk
    cc0
    nfcv
    nfif
    @38
    @3
    wceq
    @68
    @4
    cB
    @5
    cc0
    @38
    @3
    cA
    eleq1
    vk
    @3
    cB
    csbeq1a
    ifbieq1d
    cbvmpt
    eqcomi
    fvmpts
    syl2anc
    @77
    eqtr4d
    seqfeq
    breq1d
    bitrd
    iotabidv
    vx
    cA
    cB
    vf
    vk
    vm
    vn
    df-sum
    vx
    @25
    cli
    df-fv
    3eqtr4g
end

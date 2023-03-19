include "cfv.mm"
include "cv.mm"
include "crsp.mm"
include "wceq.mm"
include "cpw.mm"
include "cfn.mm"
include "cin.mm"
include "wrex.mm"
include "wss.mm"
include "clnr.mm"
include "wcel.mm"
include "clidl.mm"
include "crg.mm"
include "cn0.mm"
include "lnrring.mm"
include "syl.mm"
include "eqid.mm"
include "hbtlem2.mm"
include "syl3anc.mm"
include "lnr2i.mm"
include "syl2anc.mm"
include "wa.mm"
include "elfpw.mm"
include "cdg1.mm"
include "cle.mm"
include "wbr.mm"
include "crab.mm"
include "cco1.mm"
include "cmpt.mm"
include "cima.mm"
include "wfn.mm"
include "crn.mm"
include "fvex.mm"
include "fnmpti.mm"
include "a1i.mm"
include "simprl.mm"
include "cab.mm"
include "hbtlem1.mm"
include "rnmpt.mm"
include "fveq2.mm"
include "breq1d.mm"
include "rexrab.mm"
include "abbii.mm"
include "eqtri.mm"
include "syl6eqr.mm"
include "adantr.mm"
include "sseqtrd.mm"
include "simprr.mm"
include "fipreima.mm"
include "wi.mm"
include "ssrab2.mm"
include "sstr2.mm"
include "mpi.mm"
include "adantl.mm"
include "selpw.mm"
include "sylibr.mm"
include "adantrr.mm"
include "elind.mm"
include "cbs.mm"
include "ply1ring.mm"
include "syl6ss.mm"
include "lidlss.mm"
include "sstrd.mm"
include "rspcl.mm"
include "cres.mm"
include "df-ima.mm"
include "wral.mm"
include "rspssid.mm"
include "ssrab.mm"
include "simprbi.mm"
include "ad2antrl.mm"
include "sylanbrc.mm"
include "resmptd.mm"
include "resmpt.mm"
include "eqtr4d.mm"
include "resss.mm"
include "syl6eqssr.mm"
include "rnss.mm"
include "syl5eqss.mm"
include "sseqtr4d.mm"
include "rspssp.mm"
include "jca.mm"
include "sseq1d.mm"
include "anbi2d.mm"
include "syl5ibcom.mm"
include "sylan2b.mm"
include "expimpd.mm"
include "reximdv2.mm"
include "mpd.mm"
include "sseq1.mm"
include "rexbidv.mm"
include "syl5ibrcom.mm"
include "rexlimdva.mm"

theorem hbtlem6
  let wph: wff ph
  let cP: class P
  let cR: class R
  let cS: class S
  let cU: class U
  let vk: setvar k
  let cI: class I
  let cN: class N
  let cX: class X
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d
  let ve: setvar e
  assume hbtlem.p: |- P = ( Poly1 ` R )
  assume hbtlem.u: |- U = ( LIdeal ` P )
  assume hbtlem.s: |- S = ( ldgIdlSeq ` R )
  assume hbtlem6.n: |- N = ( RSpan ` P )
  assume hbtlem6.r: |- ( ph -> R e. LNoeR )
  assume hbtlem6.i: |- ( ph -> I e. U )
  assume hbtlem6.x: |- ( ph -> X e. NN0 )

  disjoint k ph
  disjoint I k
  disjoint R k
  disjoint S k
  disjoint X k
  disjoint a ph
  disjoint a k
  disjoint I a
  disjoint I b
  disjoint I c
  disjoint I d
  disjoint b c
  disjoint b d
  disjoint c d
  disjoint N a
  disjoint N b
  disjoint N c
  disjoint N e
  disjoint b e
  disjoint c e
  disjoint R a
  disjoint R b
  disjoint R c
  disjoint R d
  disjoint R e
  disjoint S a
  disjoint X a
  disjoint X b
  disjoint X c
  disjoint X d
  disjoint X e
  disjoint b k
  disjoint c k
  disjoint e k
  assert |- ( ph -> E. k e. ( ~P I i^i Fin ) ( ( S ` I ) ` X ) C_ ( ( S ` ( N ` k ) ) ` X ) )

  proof
    wph
    cX
    cI
    cS
    cfv
    cfv
    #
    va
    cv
    #
    cR
    crsp
    cfv
    #
    cfv
    #
    wceq
    #
    va
    @0
    cpw
    cfn
    cin
    #
    wrex
    #
    @0
    cX
    vk
    cv
    #
    cN
    cfv
    #
    cS
    cfv
    cfv
    #
    wss
    #
    vk
    cI
    cpw
    #
    cfn
    cin
    #
    wrex
    #
    wph
    cR
    clnr
    wcel
    #
    @0
    cR
    clidl
    cfv
    #
    wcel
    #
    @6
    hbtlem6.r
    wph
    cR
    crg
    wcel
    #
    cI
    cU
    wcel
    #
    cX
    cn0
    wcel
    #
    @16
    wph
    @14
    @17
    hbtlem6.r
    cR
    lnrring
    syl
    #
    hbtlem6.i
    hbtlem6.x
    cP
    cR
    cS
    @15
    cU
    cI
    cX
    hbtlem.p
    hbtlem.u
    hbtlem.s
    @15
    eqid
    #
    hbtlem2
    syl3anc
    cR
    @15
    va
    @0
    @2
    @21
    @2
    eqid
    #
    lnr2i
    syl2anc
    wph
    @4
    @13
    va
    @5
    wph
    @1
    @5
    wcel
    #
    wa
    @13
    @4
    @3
    @9
    wss
    #
    vk
    @12
    wrex
    #
    @23
    wph
    @1
    @0
    wss
    #
    @1
    cfn
    wcel
    #
    wa
    #
    @25
    @1
    @0
    elfpw
    wph
    @28
    wa
    #
    vb
    vc
    cv
    #
    cR
    cdg1
    cfv
    #
    cfv
    #
    cX
    cle
    wbr
    #
    vc
    cI
    crab
    #
    cX
    vb
    cv
    #
    cco1
    cfv
    #
    cfv
    #
    cmpt
    #
    @7
    cima
    #
    @1
    wceq
    #
    vk
    @34
    cpw
    cfn
    cin
    #
    wrex
    #
    @25
    @29
    @38
    @34
    wfn
    #
    @1
    @38
    crn
    #
    wss
    @27
    @42
    @43
    @29
    vb
    @34
    @37
    @38
    cX
    @36
    fvex
    @38
    eqid
    #
    fnmpti
    a1i
    @29
    @1
    @0
    @44
    wph
    @26
    @27
    simprl
    wph
    @0
    @44
    wceq
    @28
    wph
    @0
    @35
    @31
    cfv
    #
    cX
    cle
    wbr
    #
    vd
    cv
    @37
    wceq
    #
    wa
    vb
    cI
    wrex
    #
    vd
    cab
    #
    @44
    wph
    @14
    @18
    @19
    @0
    @50
    wceq
    hbtlem6.r
    hbtlem6.i
    hbtlem6.x
    @31
    cP
    cR
    cS
    cU
    vd
    vb
    cI
    clnr
    cX
    hbtlem.p
    hbtlem.u
    hbtlem.s
    @31
    eqid
    #
    hbtlem1
    syl3anc
    @44
    @48
    vb
    @34
    wrex
    #
    vd
    cab
    @50
    vb
    vd
    @34
    @37
    @38
    @45
    rnmpt
    @52
    @49
    vd
    @33
    @47
    @48
    vb
    vc
    cI
    @30
    @35
    wceq
    @32
    @46
    cX
    cle
    @30
    @35
    @31
    fveq2
    breq1d
    #
    rexrab
    abbii
    eqtri
    syl6eqr
    adantr
    sseqtrd
    wph
    @26
    @27
    simprr
    @1
    @34
    @38
    vk
    fipreima
    syl3anc
    @29
    @40
    @24
    vk
    @41
    @12
    wph
    @7
    @41
    wcel
    #
    @40
    wa
    @7
    @12
    wcel
    #
    @24
    wa
    #
    wi
    @28
    wph
    @54
    @40
    @56
    @54
    wph
    @7
    @34
    wss
    #
    @7
    cfn
    wcel
    #
    wa
    #
    @40
    @56
    wi
    @7
    @34
    elfpw
    wph
    @59
    wa
    #
    @55
    @39
    @2
    cfv
    #
    @9
    wss
    #
    wa
    @40
    @56
    @60
    @55
    @62
    @60
    @11
    cfn
    @7
    wph
    @57
    @7
    @11
    wcel
    #
    @58
    wph
    @57
    wa
    @7
    cI
    wss
    #
    @63
    @57
    @64
    wph
    @57
    @34
    cI
    wss
    @64
    @33
    vc
    cI
    ssrab2
    #
    @7
    @34
    cI
    sstr2
    mpi
    adantl
    vk
    cI
    selpw
    sylibr
    adantrr
    wph
    @57
    @58
    simprr
    elind
    @60
    @17
    @9
    @15
    wcel
    #
    @39
    @9
    wss
    @62
    wph
    @17
    @59
    @20
    adantr
    #
    @60
    @17
    @8
    cU
    wcel
    #
    @19
    @66
    @67
    @60
    cP
    crg
    wcel
    #
    @7
    cP
    cbs
    cfv
    #
    wss
    #
    @68
    wph
    @69
    @59
    wph
    @17
    @69
    @20
    cP
    cR
    hbtlem.p
    ply1ring
    syl
    adantr
    #
    @60
    @7
    cI
    @70
    @60
    @7
    @34
    cI
    wph
    @57
    @58
    simprl
    @65
    syl6ss
    wph
    cI
    @70
    wss
    #
    @59
    wph
    @18
    @73
    hbtlem6.i
    @70
    cI
    cU
    cP
    @70
    eqid
    #
    hbtlem.u
    lidlss
    syl
    adantr
    sstrd
    #
    @70
    cP
    cU
    @7
    cN
    hbtlem6.n
    @74
    hbtlem.u
    rspcl
    syl2anc
    #
    wph
    @19
    @59
    hbtlem6.x
    adantr
    #
    cP
    cR
    cS
    @15
    cU
    @8
    cX
    hbtlem.p
    hbtlem.u
    hbtlem.s
    @21
    hbtlem2
    syl3anc
    @60
    @39
    vb
    @33
    vc
    @8
    crab
    #
    @37
    cmpt
    #
    crn
    #
    @9
    @60
    @39
    @38
    @7
    cres
    #
    crn
    #
    @80
    @38
    @7
    df-ima
    @60
    @81
    @79
    wss
    @82
    @80
    wss
    @60
    @81
    @79
    @7
    cres
    #
    @79
    @60
    @83
    vb
    @7
    @37
    cmpt
    #
    @81
    @60
    vb
    @78
    @7
    @37
    @60
    @7
    @8
    wss
    #
    @33
    vc
    @7
    wral
    #
    @7
    @78
    wss
    @60
    @69
    @71
    @85
    @72
    @75
    @70
    cP
    @7
    cN
    hbtlem6.n
    @74
    rspssid
    syl2anc
    @57
    @86
    wph
    @58
    @57
    @64
    @86
    @33
    vc
    cI
    @7
    ssrab
    simprbi
    ad2antrl
    @33
    vc
    @8
    @7
    ssrab
    sylanbrc
    resmptd
    @57
    @81
    @84
    wceq
    wph
    @58
    vb
    @34
    @7
    @37
    resmpt
    ad2antrl
    eqtr4d
    @79
    @7
    resss
    syl6eqssr
    @81
    @79
    rnss
    syl
    syl5eqss
    @60
    @9
    @47
    ve
    cv
    @37
    wceq
    #
    wa
    vb
    @8
    wrex
    #
    ve
    cab
    #
    @80
    @60
    @17
    @68
    @19
    @9
    @89
    wceq
    @67
    @76
    @77
    @31
    cP
    cR
    cS
    cU
    ve
    vb
    @8
    crg
    cX
    hbtlem.p
    hbtlem.u
    hbtlem.s
    @51
    hbtlem1
    syl3anc
    @80
    @87
    vb
    @78
    wrex
    #
    ve
    cab
    @89
    vb
    ve
    @78
    @37
    @79
    @79
    eqid
    rnmpt
    @90
    @88
    ve
    @33
    @47
    @87
    vb
    vc
    @8
    @53
    rexrab
    abbii
    eqtri
    syl6eqr
    sseqtr4d
    cR
    @15
    @39
    @9
    @2
    @22
    @21
    rspssp
    syl3anc
    jca
    @40
    @62
    @24
    @55
    @40
    @61
    @3
    @9
    @39
    @1
    @2
    fveq2
    sseq1d
    anbi2d
    syl5ibcom
    sylan2b
    expimpd
    adantr
    reximdv2
    mpd
    sylan2b
    @4
    @10
    @24
    vk
    @12
    @0
    @3
    @9
    sseq1
    rexbidv
    syl5ibrcom
    rexlimdva
    mpd
end

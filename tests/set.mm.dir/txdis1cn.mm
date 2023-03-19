include "cpw.mm"
include "ctx.mm"
include "co.mm"
include "ccn.mm"
include "wcel.mm"
include "cxp.mm"
include "cuni.mm"
include "wf.mm"
include "ccnv.mm"
include "cv.mm"
include "cima.mm"
include "wral.mm"
include "wfn.mm"
include "wa.mm"
include "cmpt.mm"
include "ctopon.mm"
include "cfv.mm"
include "adantr.mm"
include "ctop.mm"
include "eqid.mm"
include "toptopon.mm"
include "sylib.mm"
include "cnf2.mm"
include "syl3anc.mm"
include "fmpt.mm"
include "sylibr.mm"
include "ralrimiva.mm"
include "ffnov.mm"
include "sylanbrc.mm"
include "wss.mm"
include "wrex.mm"
include "cab.mm"
include "wrel.mm"
include "cdm.mm"
include "cnvimass.mm"
include "wceq.mm"
include "fndm.mm"
include "syl.mm"
include "syl5sseq.mm"
include "relxp.mm"
include "relss.mm"
include "mpisyl.mm"
include "cop.mm"
include "wb.mm"
include "elpreima.mm"
include "opelxp.mm"
include "df-ov.mm"
include "eqcomi.mm"
include "eleq1i.mm"
include "anbi12i.mm"
include "csn.mm"
include "crab.mm"
include "simprll.mm"
include "snelpwi.mm"
include "mptpreima.mm"
include "adantrr.mm"
include "ad2ant2r.mm"
include "simplr.mm"
include "cnima.mm"
include "syl2anc.mm"
include "syl5eqelr.mm"
include "simprlr.mm"
include "simprr.mm"
include "vsnid.mm"
include "mpbiran.mm"
include "weq.mm"
include "oveq2.mm"
include "eleq1d.mm"
include "elrab.mm"
include "bitri.mm"
include "a1i.mm"
include "snssd.mm"
include "sselda.mm"
include "elrabi.mm"
include "ad2antll.mm"
include "elsni.mm"
include "ad2antrl.mm"
include "oveq1d.mm"
include "syl5eqr.mm"
include "simprbi.mm"
include "eqeltrd.mm"
include "ad3antrrr.mm"
include "mpbir2and.mm"
include "ex.mm"
include "syl5bi.mm"
include "relssdv.mm"
include "xpeq1.mm"
include "eleq2d.mm"
include "sseq1d.mm"
include "anbi12d.mm"
include "xpeq2.mm"
include "rspc2ev.mm"
include "syl112anc.mm"
include "opex.mm"
include "eleq1.mm"
include "anbi1d.mm"
include "2rexbidv.mm"
include "elab.mm"
include "sylbid.mm"
include "ssabral.mm"
include "distopon.mm"
include "eltx.mm"
include "mpbird.mm"
include "txtopon.mm"
include "iscn.mm"

theorem txdis1cn
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cF: class F
  let cJ: class J
  let cK: class K
  let cV: class V
  let cX: class X
  let cY: class Y
  let va: setvar a
  let vb: setvar b
  let vm: setvar m
  let vn: setvar n
  let vu: setvar u
  let vv: setvar v
  let vz: setvar z
  assume txdis1cn.x: |- ( ph -> X e. V )
  assume txdis1cn.j: |- ( ph -> J e. ( TopOn ` Y ) )
  assume txdis1cn.k: |- ( ph -> K e. Top )
  assume txdis1cn.f: |- ( ph -> F Fn ( X X. Y ) )
  assume txdis1cn.1: |- ( ( ph /\ x e. X ) -> ( y e. Y |-> ( x F y ) ) e. ( J Cn K ) )

  disjoint x y
  disjoint F x
  disjoint F y
  disjoint J x
  disjoint X x
  disjoint X y
  disjoint K x
  disjoint K y
  disjoint ph x
  disjoint Y x
  disjoint Y y
  disjoint a b
  disjoint a m
  disjoint a n
  disjoint a u
  disjoint a v
  disjoint a x
  disjoint a y
  disjoint a z
  disjoint F a
  disjoint b m
  disjoint b n
  disjoint b u
  disjoint b v
  disjoint b x
  disjoint b y
  disjoint b z
  disjoint F b
  disjoint m n
  disjoint m u
  disjoint m v
  disjoint m x
  disjoint m y
  disjoint m z
  disjoint F m
  disjoint n u
  disjoint n v
  disjoint n x
  disjoint n y
  disjoint n z
  disjoint F n
  disjoint u v
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint F u
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint F v
  disjoint x z
  disjoint y z
  disjoint F z
  disjoint J a
  disjoint J b
  disjoint J u
  disjoint J v
  disjoint J z
  disjoint X a
  disjoint X b
  disjoint X m
  disjoint X n
  disjoint X u
  disjoint X v
  disjoint X z
  disjoint K m
  disjoint K n
  disjoint K u
  disjoint K z
  disjoint m ph
  disjoint n ph
  disjoint ph u
  disjoint ph z
  disjoint Y b
  disjoint Y m
  disjoint Y n
  disjoint Y u
  assert |- ( ph -> F e. ( ( ~P X tX J ) Cn K ) )

  proof
    wph
    cF
    cX
    cpw
    #
    cJ
    ctx
    co
    #
    cK
    ccn
    co
    wcel
    #
    cX
    cY
    cxp
    #
    cK
    cuni
    #
    cF
    wf
    #
    cF
    ccnv
    vu
    cv
    #
    cima
    #
    @1
    wcel
    #
    vu
    cK
    wral
    #
    wph
    cF
    @3
    wfn
    #
    vx
    cv
    #
    vy
    cv
    #
    cF
    co
    #
    @4
    wcel
    vy
    cY
    wral
    #
    vx
    cX
    wral
    @5
    txdis1cn.f
    wph
    @14
    vx
    cX
    wph
    @11
    cX
    wcel
    #
    wa
    #
    cY
    @4
    vy
    cY
    @13
    cmpt
    #
    wf
    #
    @14
    @16
    cJ
    cY
    ctopon
    cfv
    #
    wcel
    #
    cK
    @4
    ctopon
    cfv
    wcel
    #
    @17
    cJ
    cK
    ccn
    co
    wcel
    #
    @18
    wph
    @20
    @15
    txdis1cn.j
    adantr
    wph
    @21
    @15
    wph
    cK
    ctop
    wcel
    @21
    txdis1cn.k
    cK
    @4
    @4
    eqid
    toptopon
    sylib
    #
    adantr
    txdis1cn.1
    @17
    cJ
    cK
    cY
    @4
    cnf2
    syl3anc
    vy
    cY
    @4
    @13
    @17
    @17
    eqid
    #
    fmpt
    sylibr
    ralrimiva
    vx
    vy
    cX
    cY
    @4
    cF
    ffnov
    sylanbrc
    wph
    @8
    vu
    cK
    wph
    @6
    cK
    wcel
    #
    wa
    #
    @8
    vv
    cv
    #
    va
    cv
    #
    vb
    cv
    #
    cxp
    #
    wcel
    #
    @30
    @7
    wss
    #
    wa
    #
    vb
    cJ
    wrex
    va
    @0
    wrex
    #
    vv
    @7
    wral
    #
    @26
    @7
    @34
    vv
    cab
    #
    wss
    @35
    @26
    vx
    vz
    @7
    @36
    @26
    @7
    @3
    wss
    @3
    wrel
    @7
    wrel
    @26
    cF
    cdm
    #
    @7
    @3
    cF
    @6
    cnvimass
    @26
    @10
    @37
    @3
    wceq
    wph
    @10
    @25
    txdis1cn.f
    adantr
    #
    @3
    cF
    fndm
    syl
    syl5sseq
    cX
    cY
    relxp
    @7
    @3
    relss
    mpisyl
    @26
    @11
    vz
    cv
    #
    cop
    #
    @7
    wcel
    #
    @40
    @3
    wcel
    #
    @40
    cF
    cfv
    #
    @6
    wcel
    #
    wa
    #
    @40
    @36
    wcel
    #
    @26
    @10
    @41
    @45
    wb
    @38
    @3
    @40
    @6
    cF
    elpreima
    syl
    @45
    @15
    @39
    cY
    wcel
    #
    wa
    #
    @11
    @39
    cF
    co
    #
    @6
    wcel
    #
    wa
    #
    @26
    @46
    @42
    @48
    @44
    @50
    @11
    @39
    cX
    cY
    opelxp
    @43
    @49
    @6
    @49
    @43
    @11
    @39
    cF
    df-ov
    eqcomi
    eleq1i
    anbi12i
    @26
    @51
    @46
    @26
    @51
    wa
    #
    @40
    @30
    wcel
    #
    @32
    wa
    #
    vb
    cJ
    wrex
    va
    @0
    wrex
    #
    @46
    @52
    @11
    csn
    #
    @0
    wcel
    #
    @13
    @6
    wcel
    #
    vy
    cY
    crab
    #
    cJ
    wcel
    @40
    @56
    @59
    cxp
    #
    wcel
    #
    @60
    @7
    wss
    #
    @55
    @52
    @15
    @57
    @26
    @15
    @47
    @50
    simprll
    #
    @11
    cX
    snelpwi
    syl
    @52
    @59
    @17
    ccnv
    @6
    cima
    #
    cJ
    vy
    cY
    @13
    @6
    @17
    @24
    mptpreima
    @52
    @22
    @25
    @64
    cJ
    wcel
    wph
    @48
    @22
    @25
    @50
    wph
    @15
    @22
    @47
    txdis1cn.1
    adantrr
    ad2ant2r
    wph
    @25
    @51
    simplr
    @6
    @17
    cJ
    cK
    cnima
    syl2anc
    syl5eqelr
    @52
    @47
    @50
    @61
    @26
    @15
    @47
    @50
    simprlr
    @26
    @48
    @50
    simprr
    @61
    @39
    @59
    wcel
    #
    @47
    @50
    wa
    @61
    @11
    @56
    wcel
    @65
    vx
    vsnid
    @11
    @39
    @56
    @59
    opelxp
    mpbiran
    @58
    @50
    vy
    @39
    cY
    vy
    vz
    weq
    @13
    @49
    @6
    @12
    @39
    @11
    cF
    oveq2
    eleq1d
    elrab
    bitri
    sylanbrc
    @52
    vn
    vm
    @60
    @7
    @60
    wrel
    @52
    @56
    @59
    relxp
    a1i
    vn
    cv
    #
    vm
    cv
    #
    cop
    #
    @60
    wcel
    @66
    @56
    wcel
    #
    @67
    @59
    wcel
    #
    wa
    #
    @52
    @68
    @7
    wcel
    #
    @66
    @67
    @56
    @59
    opelxp
    @52
    @71
    @72
    @52
    @71
    wa
    #
    @72
    @68
    @3
    wcel
    #
    @68
    cF
    cfv
    #
    @6
    wcel
    #
    @73
    @66
    cX
    wcel
    #
    @67
    cY
    wcel
    #
    @74
    @52
    @69
    @77
    @70
    @52
    @56
    cX
    @66
    @52
    @11
    cX
    @63
    snssd
    sselda
    adantrr
    @70
    @78
    @52
    @69
    @58
    vy
    @67
    cY
    elrabi
    ad2antll
    @66
    @67
    cX
    cY
    opelxp
    sylanbrc
    @73
    @75
    @11
    @67
    cF
    co
    #
    @6
    @73
    @75
    @66
    @67
    cF
    co
    @79
    @66
    @67
    cF
    df-ov
    @73
    @66
    @11
    @67
    cF
    @69
    vn
    vx
    weq
    @52
    @70
    @66
    @11
    elsni
    ad2antrl
    oveq1d
    syl5eqr
    @70
    @79
    @6
    wcel
    #
    @52
    @69
    @70
    @78
    @80
    @58
    @80
    vy
    @67
    cY
    vy
    vm
    weq
    @13
    @79
    @6
    @12
    @67
    @11
    cF
    oveq2
    eleq1d
    elrab
    simprbi
    ad2antll
    eqeltrd
    wph
    @72
    @74
    @76
    wa
    wb
    #
    @25
    @51
    @71
    wph
    @10
    @81
    txdis1cn.f
    @3
    @68
    @6
    cF
    elpreima
    syl
    ad3antrrr
    mpbir2and
    ex
    syl5bi
    relssdv
    @54
    @61
    @62
    wa
    @40
    @56
    @29
    cxp
    #
    wcel
    #
    @82
    @7
    wss
    #
    wa
    va
    vb
    @56
    @59
    @0
    cJ
    @28
    @56
    wceq
    #
    @53
    @83
    @32
    @84
    @85
    @30
    @82
    @40
    @28
    @56
    @29
    xpeq1
    #
    eleq2d
    @85
    @30
    @82
    @7
    @86
    sseq1d
    anbi12d
    @29
    @59
    wceq
    #
    @83
    @61
    @84
    @62
    @87
    @82
    @60
    @40
    @29
    @59
    @56
    xpeq2
    #
    eleq2d
    @87
    @82
    @60
    @7
    @88
    sseq1d
    anbi12d
    rspc2ev
    syl112anc
    @34
    @55
    vv
    @40
    @11
    @39
    opex
    @27
    @40
    wceq
    #
    @33
    @54
    va
    vb
    @0
    cJ
    @89
    @31
    @53
    @32
    @27
    @40
    @30
    eleq1
    anbi1d
    2rexbidv
    elab
    sylibr
    ex
    syl5bi
    sylbid
    relssdv
    @34
    vv
    @7
    ssabral
    sylib
    @26
    @0
    cX
    ctopon
    cfv
    #
    wcel
    #
    @20
    @8
    @35
    wb
    wph
    @91
    @25
    wph
    cX
    cV
    wcel
    @91
    txdis1cn.x
    cX
    cV
    distopon
    syl
    #
    adantr
    wph
    @20
    @25
    txdis1cn.j
    adantr
    va
    vb
    @7
    @0
    cJ
    @90
    @19
    vv
    eltx
    syl2anc
    mpbird
    ralrimiva
    wph
    @1
    @3
    ctopon
    cfv
    wcel
    #
    @21
    @2
    @5
    @9
    wa
    wb
    wph
    @91
    @20
    @93
    @92
    txdis1cn.j
    @0
    cJ
    cX
    cY
    txtopon
    syl2anc
    @23
    vu
    cF
    @1
    cK
    @3
    @4
    iscn
    syl2anc
    mpbir2and
end

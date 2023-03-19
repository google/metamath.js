include "ctopon.mm"
include "cfv.mm"
include "wcel.mm"
include "ccld.mm"
include "wceq.mm"
include "ctop.mm"
include "cuni.mm"
include "cv.mm"
include "wss.mm"
include "wi.mm"
include "wal.mm"
include "cin.mm"
include "wral.mm"
include "wa.mm"
include "c0.mm"
include "unieq.mm"
include "uni0.mm"
include "syl6eq.mm"
include "eleq1d.mm"
include "wne.mm"
include "cpw.mm"
include "cdif.mm"
include "crab.mm"
include "ssrab2.mm"
include "eqsstri.mm"
include "sstr.mm"
include "mpan2.mm"
include "adantl.mm"
include "sspwuni.mm"
include "sylib.mm"
include "vuniex.mm"
include "elpw.mm"
include "sylibr.mm"
include "adantr.mm"
include "ciun.mm"
include "uniiun.mm"
include "difeq2i.mm"
include "ciin.mm"
include "iindif2.mm"
include "cmre.mm"
include "ad2antrr.mm"
include "simpr.mm"
include "weq.mm"
include "difeq2.mm"
include "elrab2.mm"
include "simprbi.mm"
include "rgen.mm"
include "ssralv.mm"
include "mpi.mm"
include "mreiincl.mm"
include "syl3anc.mm"
include "eqeltrrd.mm"
include "syl5eqel.mm"
include "sylanbrc.mm"
include "0elpw.mm"
include "a1i.mm"
include "mre1cl.mm"
include "syl.mm"
include "dif0.mm"
include "pm2.61ne.mm"
include "ex.mm"
include "alrimiv.mm"
include "inss1.mm"
include "simplbi.mm"
include "elpwid.mm"
include "ad2antrl.mm"
include "syl5ss.mm"
include "vex.mm"
include "inex1.mm"
include "cun.mm"
include "difindi.mm"
include "ad2antll.mm"
include "simpl.mm"
include "uneq1.mm"
include "imbi2d.mm"
include "uneq2.mm"
include "3expb.mm"
include "expcom.mm"
include "vtocl2ga.mm"
include "imp.mm"
include "syl21anc.mm"
include "ralrimivva.mm"
include "cvv.mm"
include "wb.mm"
include "pwexg.mm"
include "rabexd.mm"
include "istopg.mm"
include "mpbir2and.mm"
include "unissi.mm"
include "unipw.mm"
include "sseqtri.mm"
include "pwidg.mm"
include "difid.mm"
include "unissel.mm"
include "sylancr.mm"
include "eqcomd.mm"
include "istopon.mm"
include "eqid.mm"
include "cldval.mm"
include "pweqd.mm"
include "difeq1d.mm"
include "rabeqbidv.mm"
include "eleq2i.mm"
include "difss.mm"
include "elpw2g.mm"
include "mpbiri.mm"
include "elrab3.mm"
include "syl5bb.mm"
include "elpwi.mm"
include "dfss4.mm"
include "bitrd.mm"
include "rabbidva.mm"
include "incom.mm"
include "dfin5.mm"
include "eqtri.mm"
include "mresspw.mm"
include "df-ss.mm"
include "syl5eqr.mm"
include "eqtrd.mm"
include "3eqtrrd.mm"
include "jca.mm"

theorem mretopd
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cB: class B
  let cJ: class J
  let cM: class M
  let va: setvar a
  let vb: setvar b
  assume mretopd.m: |- ( ph -> M e. ( Moore ` B ) )
  assume mretopd.z: |- ( ph -> (/) e. M )
  assume mretopd.u: |- ( ( ph /\ x e. M /\ y e. M ) -> ( x u. y ) e. M )
  assume mretopd.j: |- J = { z e. ~P B | ( B \ z ) e. M }

  disjoint ph x
  disjoint ph y
  disjoint ph z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint M x
  disjoint M y
  disjoint M z
  disjoint J x
  disjoint J y
  disjoint B x
  disjoint B y
  disjoint B z
  disjoint a ph
  disjoint b ph
  disjoint a b
  disjoint a x
  disjoint a y
  disjoint a z
  disjoint b x
  disjoint b y
  disjoint b z
  disjoint M a
  disjoint M b
  disjoint J a
  disjoint J b
  disjoint B a
  disjoint B b
  assert |- ( ph -> ( J e. ( TopOn ` B ) /\ M = ( Clsd ` J ) ) )

  proof
    wph
    cJ
    cB
    ctopon
    cfv
    wcel
    #
    cM
    cJ
    ccld
    cfv
    #
    wceq
    wph
    cJ
    ctop
    wcel
    #
    cB
    cJ
    cuni
    #
    wceq
    @0
    wph
    @2
    va
    cv
    #
    cJ
    wss
    #
    @4
    cuni
    #
    cJ
    wcel
    #
    wi
    #
    va
    wal
    #
    @4
    vb
    cv
    #
    cin
    #
    cJ
    wcel
    #
    vb
    cJ
    wral
    va
    cJ
    wral
    #
    wph
    @8
    va
    wph
    @5
    @7
    wph
    @5
    wa
    #
    @7
    c0
    cJ
    wcel
    #
    @4
    c0
    @4
    c0
    wceq
    #
    @6
    c0
    cJ
    @16
    @6
    c0
    cuni
    c0
    @4
    c0
    unieq
    uni0
    syl6eq
    eleq1d
    @14
    @4
    c0
    wne
    #
    wa
    #
    @6
    cB
    cpw
    #
    wcel
    #
    cB
    @6
    cdif
    #
    cM
    wcel
    #
    @7
    @14
    @20
    @17
    @14
    @6
    cB
    wss
    #
    @20
    @14
    @4
    @19
    wss
    #
    @23
    @5
    @24
    wph
    @5
    cJ
    @19
    wss
    @24
    cJ
    cB
    vz
    cv
    #
    cdif
    #
    cM
    wcel
    #
    vz
    @19
    crab
    #
    @19
    mretopd.j
    @27
    vz
    @19
    ssrab2
    eqsstri
    #
    @4
    cJ
    @19
    sstr
    mpan2
    adantl
    @4
    cB
    sspwuni
    sylib
    @6
    cB
    va
    vuniex
    elpw
    sylibr
    adantr
    @18
    @21
    cB
    vb
    @4
    @10
    ciun
    #
    cdif
    #
    cM
    @6
    @30
    cB
    vb
    @4
    uniiun
    difeq2i
    @18
    vb
    @4
    cB
    @10
    cdif
    #
    ciin
    #
    @31
    cM
    @17
    @33
    @31
    wceq
    @14
    vb
    @4
    cB
    @10
    iindif2
    adantl
    @18
    cM
    cB
    cmre
    cfv
    wcel
    #
    @17
    @32
    cM
    wcel
    #
    vb
    @4
    wral
    #
    @33
    cM
    wcel
    wph
    @34
    @5
    @17
    mretopd.m
    ad2antrr
    @14
    @17
    simpr
    @14
    @36
    @17
    @14
    @35
    vb
    cJ
    wral
    #
    @36
    @35
    vb
    cJ
    @10
    cJ
    wcel
    #
    @10
    @19
    wcel
    @35
    @27
    @35
    vz
    @10
    @19
    cJ
    vz
    vb
    weq
    @26
    @32
    cM
    @25
    @10
    cB
    difeq2
    eleq1d
    mretopd.j
    elrab2
    simprbi
    #
    rgen
    @5
    @37
    @36
    wi
    wph
    @35
    vb
    @4
    cJ
    ssralv
    adantl
    mpi
    adantr
    vb
    cM
    @32
    @4
    cB
    mreiincl
    syl3anc
    eqeltrrd
    syl5eqel
    @27
    @22
    vz
    @6
    @19
    cJ
    @25
    @6
    wceq
    @26
    @21
    cM
    @25
    @6
    cB
    difeq2
    eleq1d
    mretopd.j
    elrab2
    sylanbrc
    wph
    @15
    @5
    wph
    c0
    @19
    wcel
    #
    cB
    cM
    wcel
    #
    @15
    @40
    wph
    cB
    0elpw
    a1i
    wph
    @34
    @41
    mretopd.m
    cM
    cB
    mre1cl
    syl
    #
    @27
    @41
    vz
    c0
    @19
    cJ
    @25
    c0
    wceq
    #
    @26
    cB
    cM
    @43
    @26
    cB
    c0
    cdif
    cB
    @25
    c0
    cB
    difeq2
    cB
    dif0
    syl6eq
    eleq1d
    mretopd.j
    elrab2
    sylanbrc
    adantr
    pm2.61ne
    ex
    alrimiv
    wph
    @12
    va
    vb
    cJ
    cJ
    wph
    @4
    cJ
    wcel
    #
    @38
    wa
    #
    wa
    #
    @11
    @19
    wcel
    #
    cB
    @11
    cdif
    #
    cM
    wcel
    #
    @12
    @46
    @11
    cB
    wss
    @47
    @46
    @11
    @4
    cB
    @4
    @10
    inss1
    @44
    @4
    cB
    wss
    wph
    @38
    @44
    @4
    cB
    @44
    @4
    @19
    wcel
    #
    cB
    @4
    cdif
    #
    cM
    wcel
    #
    @27
    @52
    vz
    @4
    @19
    cJ
    vz
    va
    weq
    @26
    @51
    cM
    @25
    @4
    cB
    difeq2
    eleq1d
    mretopd.j
    elrab2
    #
    simplbi
    elpwid
    ad2antrl
    syl5ss
    @11
    cB
    @4
    @10
    va
    vex
    inex1
    elpw
    sylibr
    @46
    @48
    @51
    @32
    cun
    #
    cM
    cB
    @4
    @10
    difindi
    @46
    @52
    @35
    wph
    @54
    cM
    wcel
    #
    @44
    @52
    wph
    @38
    @44
    @50
    @52
    @53
    simprbi
    ad2antrl
    @38
    @35
    wph
    @44
    @39
    ad2antll
    wph
    @45
    simpl
    @52
    @35
    wa
    wph
    @55
    wph
    vx
    cv
    #
    vy
    cv
    #
    cun
    #
    cM
    wcel
    #
    wi
    wph
    @51
    @57
    cun
    #
    cM
    wcel
    #
    wi
    wph
    @55
    wi
    vx
    vy
    @51
    @32
    cM
    cM
    @56
    @51
    wceq
    #
    @59
    @61
    wph
    @62
    @58
    @60
    cM
    @56
    @51
    @57
    uneq1
    eleq1d
    imbi2d
    @57
    @32
    wceq
    #
    @61
    @55
    wph
    @63
    @60
    @54
    cM
    @57
    @32
    @51
    uneq2
    eleq1d
    imbi2d
    wph
    @56
    cM
    wcel
    #
    @57
    cM
    wcel
    #
    wa
    @59
    wph
    @64
    @65
    @59
    mretopd.u
    3expb
    expcom
    vtocl2ga
    imp
    syl21anc
    syl5eqel
    @27
    @49
    vz
    @11
    @19
    cJ
    @25
    @11
    wceq
    @26
    @48
    cM
    @25
    @11
    cB
    difeq2
    eleq1d
    mretopd.j
    elrab2
    sylanbrc
    ralrimivva
    wph
    cJ
    cvv
    wcel
    @2
    @9
    @13
    wa
    wb
    wph
    @27
    vz
    @19
    cJ
    cvv
    mretopd.j
    wph
    @41
    @19
    cvv
    wcel
    @42
    cB
    cM
    pwexg
    syl
    rabexd
    va
    vb
    cvv
    cJ
    istopg
    syl
    mpbir2and
    #
    wph
    @3
    cB
    wph
    @3
    cB
    wss
    cB
    cJ
    wcel
    #
    @3
    cB
    wceq
    @3
    @19
    cuni
    cB
    cJ
    @19
    @29
    unissi
    cB
    unipw
    sseqtri
    wph
    cB
    @19
    wcel
    #
    cB
    cB
    cdif
    #
    cM
    wcel
    #
    @67
    wph
    @41
    @68
    @42
    cB
    cM
    pwidg
    syl
    wph
    @69
    c0
    cM
    cB
    difid
    mretopd.z
    syl5eqel
    @27
    @70
    vz
    cB
    @19
    cJ
    @25
    cB
    wceq
    @26
    @69
    cM
    @25
    cB
    cB
    difeq2
    eleq1d
    mretopd.j
    elrab2
    sylanbrc
    cJ
    cB
    unissel
    sylancr
    #
    eqcomd
    cB
    cJ
    istopon
    sylanbrc
    wph
    @1
    @3
    @56
    cdif
    #
    cJ
    wcel
    #
    vx
    @3
    cpw
    #
    crab
    #
    cB
    @56
    cdif
    #
    cJ
    wcel
    #
    vx
    @19
    crab
    #
    cM
    wph
    @2
    @1
    @75
    wceq
    @66
    vx
    cJ
    @3
    @3
    eqid
    cldval
    syl
    wph
    @73
    @77
    vx
    @74
    @19
    wph
    @3
    cB
    @71
    pweqd
    wph
    @72
    @76
    cJ
    wph
    @3
    cB
    @56
    @71
    difeq1d
    eleq1d
    rabeqbidv
    wph
    @78
    @64
    vx
    @19
    crab
    #
    cM
    wph
    @77
    @64
    vx
    @19
    wph
    @56
    @19
    wcel
    #
    wa
    #
    @77
    cB
    @76
    cdif
    #
    cM
    wcel
    #
    @64
    @77
    @76
    @28
    wcel
    #
    @81
    @83
    cJ
    @28
    @76
    mretopd.j
    eleq2i
    wph
    @84
    @83
    wb
    #
    @80
    wph
    @76
    @19
    wcel
    #
    @85
    wph
    @86
    @76
    cB
    wss
    #
    cB
    @56
    difss
    wph
    @41
    @86
    @87
    wb
    @42
    @76
    cB
    cM
    elpw2g
    syl
    mpbiri
    @27
    @83
    vz
    @76
    @19
    @25
    @76
    wceq
    @26
    @82
    cM
    @25
    @76
    cB
    difeq2
    eleq1d
    elrab3
    syl
    adantr
    syl5bb
    @81
    @82
    @56
    cM
    @80
    @82
    @56
    wceq
    #
    wph
    @80
    @56
    cB
    wss
    @88
    @56
    cB
    elpwi
    @56
    cB
    dfss4
    sylib
    adantl
    eleq1d
    bitrd
    rabbidva
    wph
    @79
    cM
    @19
    cin
    #
    cM
    @89
    @19
    cM
    cin
    @79
    cM
    @19
    incom
    vx
    @19
    cM
    dfin5
    eqtri
    wph
    cM
    @19
    wss
    #
    @89
    cM
    wceq
    wph
    @34
    @90
    mretopd.m
    cM
    cB
    mresspw
    syl
    cM
    @19
    df-ss
    sylib
    syl5eqr
    eqtrd
    3eqtrrd
    jca
end

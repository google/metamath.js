include "cr.mm"
include "wcel.mm"
include "climc.mm"
include "co.mm"
include "wn.mm"
include "adantr.mm"
include "wa.mm"
include "cc.mm"
include "cv.mm"
include "wne.mm"
include "cmin.mm"
include "cabs.mm"
include "cfv.mm"
include "clt.mm"
include "wbr.mm"
include "wi.mm"
include "wral.mm"
include "crp.mm"
include "wrex.mm"
include "limccl.mm"
include "sseldi.mm"
include "simpr.mm"
include "eldifd.mm"
include "dstregt0.mm"
include "csn.mm"
include "ccom.mm"
include "cbl.mm"
include "cdif.mm"
include "cxmt.mm"
include "wss.mm"
include "ccnfld.mm"
include "ctopn.mm"
include "clp.mm"
include "cnxmet.mm"
include "a1i.mm"
include "ad4antr.mm"
include "ssdifssd.mm"
include "ctop.mm"
include "cuni.mm"
include "wb.mm"
include "eqid.mm"
include "cnfldtop.mm"
include "unicntop.mm"
include "syl6sseq.mm"
include "lpdifsn.mm"
include "syl2anc.mm"
include "mpbid.mm"
include "cnfldtopn.mm"
include "lpbl.mm"
include "syl31anc.mm"
include "eldif.mm"
include "anbi1i.mm"
include "anass.mm"
include "bitri.mm"
include "rexbii2.mm"
include "sylib.mm"
include "simprl.mm"
include "velsn.mm"
include "necon3bbii.mm"
include "simp-5l.mm"
include "simplr.mm"
include "simprr.mm"
include "w3a.mm"
include "simp3.mm"
include "cxr.mm"
include "lpss.mm"
include "sseldd.mm"
include "3ad2ant1.mm"
include "rpxr.mm"
include "3ad2ant2.mm"
include "elbl.mm"
include "syl3anc.mm"
include "simpld.mm"
include "abssubd.mm"
include "wceq.mm"
include "cnmetdval.mm"
include "simprd.mm"
include "eqbrtrrd.mm"
include "eqbrtrd.mm"
include "jca.mm"
include "adantlr.mm"
include "simp-5r.mm"
include "simp-4r.mm"
include "rpre.mm"
include "ad2antlr.mm"
include "ffvelrnda.mm"
include "recnd.mm"
include "ad2antrr.mm"
include "ad3antrrr.mm"
include "subcld.mm"
include "abscld.mm"
include "nfv.mm"
include "nfra1.mm"
include "nfan.mm"
include "rspa.mm"
include "adantll.mm"
include "ax-resscn.mm"
include "sselda.mm"
include "breqtrd.mm"
include "ex.mm"
include "ralrimi.mm"
include "oveq1.mm"
include "fveq2d.mm"
include "breq2d.mm"
include "rspcv.mm"
include "sylc.mm"
include "ltnsymd.mm"
include "syl21anc.mm"
include "jcn.mm"
include "reximdva.mm"
include "mpd.mm"
include "rexnal.mm"
include "nrexdv.mm"
include "intnand.mm"
include "fssd.mm"
include "ellimc3.mm"
include "mtbird.mm"
include "condan.mm"

theorem limcrecl
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cF: class F
  let cL: class L
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  assume limcrecl.1: |- ( ph -> F : A --> RR )
  assume limcrecl.2: |- ( ph -> A C_ CC )
  assume limcrecl.3: |- ( ph -> B e. ( ( limPt ` ( TopOpen ` CCfld ) ) ` A ) )
  assume limcrecl.4: |- ( ph -> L e. ( F limCC B ) )


  assert |- ( ph -> L e. RR )

  proof
    wph
    cL
    cr
    wcel
    #
    cL
    cF
    cB
    climc
    co
    #
    wcel
    #
    wph
    @2
    @0
    wn
    #
    limcrecl.4
    adantr
    wph
    @3
    wa
    #
    @2
    cL
    cc
    wcel
    #
    vz
    cv
    #
    cB
    wne
    #
    @6
    cB
    cmin
    co
    cabs
    cfv
    #
    vy
    cv
    #
    clt
    wbr
    #
    wa
    #
    @6
    cF
    cfv
    #
    cL
    cmin
    co
    #
    cabs
    cfv
    #
    vx
    cv
    #
    clt
    wbr
    #
    wi
    #
    vz
    cA
    wral
    #
    vy
    crp
    wrex
    #
    vx
    crp
    wral
    #
    wa
    #
    @4
    @20
    @5
    @4
    @19
    wn
    #
    vx
    crp
    wrex
    #
    @20
    wn
    @4
    @15
    cL
    vw
    cv
    #
    cmin
    co
    cabs
    cfv
    #
    clt
    wbr
    #
    vw
    cr
    wral
    #
    vx
    crp
    wrex
    @23
    @4
    vx
    vw
    cL
    @4
    cL
    cc
    cr
    wph
    @5
    @3
    wph
    @1
    cc
    cL
    cB
    cF
    limccl
    limcrecl.4
    sseldi
    #
    adantr
    wph
    @3
    simpr
    eldifd
    dstregt0
    @4
    @27
    @22
    vx
    crp
    @4
    @15
    crp
    wcel
    #
    wa
    #
    @27
    @22
    @30
    @27
    wa
    #
    @18
    vy
    crp
    @31
    @9
    crp
    wcel
    #
    wa
    #
    @17
    wn
    #
    vz
    cA
    wrex
    #
    @18
    wn
    @33
    @6
    cB
    csn
    #
    wcel
    #
    wn
    #
    @6
    cB
    @9
    cabs
    cmin
    ccom
    #
    cbl
    cfv
    co
    wcel
    #
    wa
    #
    vz
    cA
    wrex
    #
    @35
    @33
    @40
    vz
    cA
    @36
    cdif
    #
    wrex
    #
    @42
    @33
    @39
    cc
    cxmt
    cfv
    wcel
    #
    @43
    cc
    wss
    cB
    @43
    ccnfld
    ctopn
    cfv
    #
    clp
    cfv
    #
    cfv
    wcel
    #
    @32
    @44
    @45
    @33
    cnxmet
    a1i
    @33
    cA
    cc
    @36
    wph
    cA
    cc
    wss
    #
    @3
    @29
    @27
    @32
    limcrecl.2
    ad4antr
    ssdifssd
    wph
    @48
    @3
    @29
    @27
    @32
    wph
    cB
    cA
    @47
    cfv
    #
    wcel
    #
    @48
    limcrecl.3
    wph
    @46
    ctop
    wcel
    #
    cA
    @46
    cuni
    #
    wss
    @51
    @48
    wb
    @52
    wph
    @46
    @46
    eqid
    #
    cnfldtop
    a1i
    #
    wph
    cA
    cc
    @53
    limcrecl.2
    unicntop
    syl6sseq
    cB
    cA
    @46
    @53
    @53
    eqid
    lpdifsn
    syl2anc
    mpbid
    ad4antr
    @31
    @32
    simpr
    vz
    @39
    cB
    @9
    @43
    @46
    cc
    @46
    @54
    cnfldtopn
    lpbl
    syl31anc
    @40
    @41
    vz
    @43
    cA
    @6
    @43
    wcel
    #
    @40
    wa
    @6
    cA
    wcel
    #
    @38
    wa
    #
    @40
    wa
    @57
    @41
    wa
    @56
    @58
    @40
    @6
    cA
    @36
    eldif
    anbi1i
    @57
    @38
    @40
    anass
    bitri
    rexbii2
    sylib
    @33
    @41
    @34
    vz
    cA
    @33
    @57
    wa
    #
    @41
    @34
    @59
    @41
    wa
    #
    @11
    @16
    @33
    @41
    @11
    @57
    @33
    @41
    wa
    #
    @7
    @10
    @61
    @38
    @7
    @33
    @38
    @40
    simprl
    @37
    @6
    cB
    vz
    cB
    velsn
    necon3bbii
    sylib
    @61
    wph
    @32
    @40
    @10
    wph
    @3
    @29
    @27
    @32
    @41
    simp-5l
    #
    @31
    @32
    @41
    simplr
    @33
    @38
    @40
    simprr
    wph
    @32
    @40
    w3a
    #
    @8
    cB
    @6
    cmin
    co
    cabs
    cfv
    #
    @9
    clt
    @63
    @6
    cB
    @63
    @6
    cc
    wcel
    #
    cB
    @6
    @39
    co
    #
    @9
    clt
    wbr
    #
    @63
    @40
    @65
    @67
    wa
    #
    wph
    @32
    @40
    simp3
    @63
    @45
    cB
    cc
    wcel
    #
    @9
    cxr
    wcel
    #
    @40
    @68
    wb
    @45
    @63
    cnxmet
    a1i
    wph
    @32
    @69
    @40
    wph
    @50
    cc
    cB
    wph
    @52
    @49
    @50
    cc
    wss
    @55
    limcrecl.2
    cA
    @46
    cc
    unicntop
    lpss
    syl2anc
    limcrecl.3
    sseldd
    #
    3ad2ant1
    #
    @32
    wph
    @70
    @40
    @9
    rpxr
    3ad2ant2
    @6
    @39
    cB
    @9
    cc
    elbl
    syl3anc
    mpbid
    #
    simpld
    #
    @72
    abssubd
    @63
    @66
    @64
    @9
    clt
    @63
    @69
    @65
    @66
    @64
    wceq
    @72
    @74
    cB
    @6
    @39
    @39
    eqid
    cnmetdval
    syl2anc
    @63
    @65
    @67
    @73
    simprd
    eqbrtrrd
    eqbrtrd
    syl3anc
    jca
    adantlr
    @60
    wph
    @57
    wa
    #
    @29
    @27
    @16
    wn
    @60
    wph
    @57
    @33
    @41
    wph
    @57
    @62
    adantlr
    @33
    @57
    @41
    simplr
    jca
    @4
    @29
    @27
    @32
    @57
    @41
    simp-5r
    @30
    @27
    @32
    @57
    @41
    simp-4r
    @75
    @29
    wa
    @27
    wa
    #
    @15
    @14
    @29
    @15
    cr
    wcel
    @75
    @27
    @15
    rpre
    ad2antlr
    @76
    @13
    @76
    @12
    cL
    @75
    @12
    cc
    wcel
    @29
    @27
    @75
    @12
    wph
    cA
    cr
    @6
    cF
    limcrecl.1
    ffvelrnda
    #
    recnd
    ad2antrr
    wph
    @5
    @57
    @29
    @27
    @28
    ad3antrrr
    subcld
    abscld
    @75
    @27
    @15
    @14
    clt
    wbr
    #
    @29
    @75
    @27
    wa
    @12
    cr
    wcel
    #
    @15
    @24
    cL
    cmin
    co
    #
    cabs
    cfv
    #
    clt
    wbr
    #
    vw
    cr
    wral
    #
    @78
    @75
    @79
    @27
    @77
    adantr
    wph
    @27
    @83
    @57
    wph
    @27
    wa
    #
    @82
    vw
    cr
    wph
    @27
    vw
    wph
    vw
    nfv
    @26
    vw
    cr
    nfra1
    nfan
    @84
    @24
    cr
    wcel
    #
    @82
    @84
    @85
    wa
    @15
    @25
    @81
    clt
    @27
    @85
    @26
    wph
    @26
    vw
    cr
    rspa
    adantll
    wph
    @85
    @25
    @81
    wceq
    @27
    wph
    @85
    wa
    cL
    @24
    wph
    @5
    @85
    @28
    adantr
    wph
    cr
    cc
    @24
    cr
    cc
    wss
    wph
    ax-resscn
    a1i
    #
    sselda
    abssubd
    adantlr
    breqtrd
    ex
    ralrimi
    adantlr
    @82
    @78
    vw
    @12
    cr
    @24
    @12
    wceq
    #
    @81
    @14
    @15
    clt
    @87
    @80
    @13
    cabs
    @24
    @12
    cL
    cmin
    oveq1
    fveq2d
    breq2d
    rspcv
    sylc
    adantlr
    ltnsymd
    syl21anc
    jcn
    ex
    reximdva
    mpd
    @17
    vz
    cA
    rexnal
    sylib
    nrexdv
    ex
    reximdva
    mpd
    @19
    vx
    crp
    rexnal
    sylib
    intnand
    wph
    @2
    @21
    wb
    @3
    wph
    vx
    vy
    vz
    cA
    cB
    cL
    cF
    wph
    cA
    cr
    cc
    cF
    limcrecl.1
    @86
    fssd
    limcrecl.2
    @71
    ellimc3
    adantr
    mtbird
    condan
end

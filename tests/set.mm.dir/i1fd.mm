include "cmbf.mm"
include "wcel.mm"
include "cr.mm"
include "wf.mm"
include "crn.mm"
include "cfn.mm"
include "ccnv.mm"
include "cc0.mm"
include "csn.mm"
include "cdif.mm"
include "cima.mm"
include "cvol.mm"
include "cfv.mm"
include "w3a.mm"
include "citg1.mm"
include "cdm.mm"
include "cv.mm"
include "cioo.mm"
include "wral.mm"
include "wa.mm"
include "wfun.mm"
include "wceq.mm"
include "ad2antrr.mm"
include "ffun.mm"
include "funcnvcnv.mm"
include "imadif.mm"
include "4syl.mm"
include "wss.mm"
include "cpw.mm"
include "cxr.mm"
include "cxp.mm"
include "ioof.mm"
include "frn.mm"
include "ax-mp.mm"
include "sseli.mm"
include "elpwid.mm"
include "ad2antlr.mm"
include "dfss4.mm"
include "sylib.mm"
include "imaeq2d.mm"
include "eqtr3d.mm"
include "fimacnv.mm"
include "syl.mm"
include "rembl.mm"
include "syl6eqel.mm"
include "wn.mm"
include "wi.mm"
include "wal.mm"
include "cin.mm"
include "ciun.mm"
include "adantr.mm"
include "inpreima.mm"
include "iunid.mm"
include "imaeq2i.mm"
include "imaiun.mm"
include "eqtr3i.mm"
include "cnvimass.mm"
include "cnvimarndm.mm"
include "sseqtr4i.mm"
include "df-ss.mm"
include "mpbi.mm"
include "3eqtr3g.mm"
include "3syl.mm"
include "inss2.mm"
include "ssfi.mm"
include "sylancl.mm"
include "simpll.mm"
include "c0.mm"
include "inss1.mm"
include "con3i.mm"
include "adantl.mm"
include "disjsn.mm"
include "sylibr.mm"
include "wb.mm"
include "reldisj.mm"
include "sselda.mm"
include "syl2anc.mm"
include "ralrimiva.mm"
include "finiunmbl.mm"
include "eqeltrrd.mm"
include "ex.mm"
include "alrimiv.mm"
include "elndif.mm"
include "cvv.mm"
include "reex.mm"
include "difexg.mm"
include "eleq2.mm"
include "notbid.mm"
include "imaeq2.mm"
include "eleq1d.mm"
include "imbi12d.mm"
include "spcv.mm"
include "sylc.mm"
include "difmbl.mm"
include "spv.mm"
include "imp.mm"
include "adantlr.mm"
include "pm2.61dan.mm"
include "ismbf.mm"
include "mpbird.mm"
include "covol.mm"
include "mblvol.mm"
include "csu.mm"
include "cle.mm"
include "wbr.mm"
include "mblss.mm"
include "fsumrecl.mm"
include "fveq2d.mm"
include "jca.mm"
include "ovolfiniun.mm"
include "eqbrtrrd.mm"
include "ovollecl.mm"
include "syl3anc.mm"
include "eqeltrd.mm"
include "neldifsn.mm"
include "mpisyl.mm"
include "3jca.mm"
include "isi1f.mm"
include "sylanbrc.mm"

theorem i1fd
  let wph: wff ph
  let vx: setvar x
  let cF: class F
  let vy: setvar y
  let vf: setvar f
  let vg: setvar g
  let cA: class A
  assume i1fd.1: |- ( ph -> F : RR --> RR )
  assume i1fd.2: |- ( ph -> ran F e. Fin )
  assume i1fd.3: |- ( ( ph /\ x e. ( ran F \ { 0 } ) ) -> ( `' F " { x } ) e. dom vol )
  assume i1fd.4: |- ( ( ph /\ x e. ( ran F \ { 0 } ) ) -> ( vol ` ( `' F " { x } ) ) e. RR )

  disjoint F x
  disjoint ph x
  disjoint F x
  disjoint x y
  disjoint F y
  disjoint ph y
  disjoint f g
  disjoint f x
  disjoint f y
  disjoint F f
  disjoint g x
  disjoint g y
  disjoint F g
  disjoint x y
  disjoint F y
  disjoint A x
  disjoint A y
  assert |- ( ph -> F e. dom S.1 )

  proof
    wph
    cF
    cmbf
    wcel
    #
    cr
    cr
    cF
    wf
    #
    cF
    crn
    #
    cfn
    wcel
    #
    cF
    ccnv
    #
    cr
    cc0
    csn
    #
    cdif
    #
    cima
    #
    cvol
    cfv
    #
    cr
    wcel
    #
    w3a
    cF
    citg1
    cdm
    wcel
    wph
    @0
    @4
    vx
    cv
    #
    cima
    #
    cvol
    cdm
    #
    wcel
    #
    vx
    cioo
    crn
    #
    wral
    #
    wph
    @13
    vx
    @14
    wph
    @10
    @14
    wcel
    #
    wa
    #
    cc0
    @10
    wcel
    #
    @13
    @17
    @18
    wa
    #
    @4
    cr
    cima
    #
    @4
    cr
    @10
    cdif
    #
    cima
    #
    cdif
    #
    @11
    @12
    @19
    @4
    cr
    @21
    cdif
    #
    cima
    #
    @23
    @11
    @19
    @1
    cF
    wfun
    #
    @4
    ccnv
    wfun
    @25
    @23
    wceq
    wph
    @1
    @16
    @18
    i1fd.1
    ad2antrr
    #
    cr
    cr
    cF
    ffun
    #
    cF
    funcnvcnv
    cr
    @21
    @4
    imadif
    4syl
    @19
    @24
    @10
    @4
    @19
    @10
    cr
    wss
    #
    @24
    @10
    wceq
    @16
    @29
    wph
    @18
    @16
    @10
    cr
    @14
    cr
    cpw
    #
    @10
    cxr
    cxr
    cxp
    #
    @30
    cioo
    wf
    @14
    @30
    wss
    ioof
    @31
    @30
    cioo
    frn
    ax-mp
    sseli
    elpwid
    ad2antlr
    @10
    cr
    dfss4
    sylib
    imaeq2d
    eqtr3d
    @19
    @20
    @12
    wcel
    @22
    @12
    wcel
    #
    @23
    @12
    wcel
    @19
    @20
    cr
    @12
    @19
    @1
    @20
    cr
    wceq
    @27
    cr
    cr
    cF
    fimacnv
    syl
    rembl
    syl6eqel
    @19
    cc0
    vy
    cv
    #
    wcel
    #
    wn
    #
    @4
    @33
    cima
    #
    @12
    wcel
    #
    wi
    #
    vy
    wal
    #
    cc0
    @21
    wcel
    #
    wn
    #
    @32
    wph
    @39
    @16
    @18
    wph
    @38
    vy
    wph
    @35
    @37
    wph
    @35
    wa
    #
    vx
    @33
    @2
    cin
    #
    @4
    @10
    csn
    #
    cima
    #
    ciun
    #
    @36
    @12
    @42
    @1
    @26
    @46
    @36
    wceq
    wph
    @1
    @35
    i1fd.1
    adantr
    @28
    @26
    @4
    @43
    cima
    #
    @36
    @4
    @2
    cima
    #
    cin
    #
    @46
    @36
    @33
    @2
    cF
    inpreima
    @4
    vx
    @43
    @44
    ciun
    #
    cima
    @47
    @46
    @50
    @43
    @4
    vx
    @43
    iunid
    imaeq2i
    vx
    @4
    @43
    @44
    imaiun
    eqtr3i
    @36
    @48
    wss
    @49
    @36
    wceq
    @36
    cF
    cdm
    @48
    cF
    @33
    cnvimass
    cF
    cnvimarndm
    sseqtr4i
    @36
    @48
    df-ss
    mpbi
    3eqtr3g
    3syl
    #
    @42
    @43
    cfn
    wcel
    #
    @45
    @12
    wcel
    #
    vx
    @43
    wral
    @46
    @12
    wcel
    @42
    @3
    @43
    @2
    wss
    #
    @52
    wph
    @3
    @35
    i1fd.2
    adantr
    @33
    @2
    inss2
    #
    @2
    @43
    ssfi
    sylancl
    #
    @42
    @53
    vx
    @43
    @42
    @10
    @43
    wcel
    #
    wa
    #
    wph
    @10
    @2
    @5
    cdif
    #
    wcel
    #
    @53
    wph
    @35
    @57
    simpll
    #
    @42
    @43
    @59
    @10
    @42
    @43
    @5
    cin
    c0
    wceq
    #
    @43
    @59
    wss
    #
    @42
    cc0
    @43
    wcel
    #
    wn
    #
    @62
    @35
    @65
    wph
    @64
    @34
    @43
    @33
    cc0
    @33
    @2
    inss1
    sseli
    con3i
    adantl
    @43
    cc0
    disjsn
    sylibr
    @54
    @62
    @63
    wb
    @55
    @43
    @5
    @2
    reldisj
    ax-mp
    sylib
    sselda
    #
    i1fd.3
    syl2anc
    #
    ralrimiva
    @43
    @45
    vx
    finiunmbl
    syl2anc
    eqeltrrd
    #
    ex
    alrimiv
    #
    ad2antrr
    @18
    @41
    @17
    cc0
    @10
    cr
    elndif
    adantl
    @38
    @41
    @32
    wi
    vy
    @21
    cr
    cvv
    wcel
    #
    @21
    cvv
    wcel
    reex
    cr
    @10
    cvv
    difexg
    ax-mp
    @33
    @21
    wceq
    #
    @35
    @41
    @37
    @32
    @71
    @34
    @40
    @33
    @21
    cc0
    eleq2
    notbid
    @71
    @36
    @22
    @12
    @33
    @21
    @4
    imaeq2
    eleq1d
    imbi12d
    spcv
    sylc
    @20
    @22
    difmbl
    syl2anc
    eqeltrrd
    wph
    @18
    wn
    #
    @13
    @16
    wph
    @72
    @13
    wph
    @39
    @72
    @13
    wi
    #
    @69
    @38
    @73
    vy
    vx
    @33
    @10
    wceq
    #
    @35
    @72
    @37
    @13
    @74
    @34
    @18
    @33
    @10
    cc0
    eleq2
    notbid
    @74
    @36
    @11
    @12
    @33
    @10
    @4
    imaeq2
    eleq1d
    imbi12d
    spv
    syl
    imp
    adantlr
    pm2.61dan
    ralrimiva
    wph
    @1
    @0
    @15
    wb
    i1fd.1
    vx
    cr
    cF
    ismbf
    syl
    mpbird
    wph
    @1
    @3
    @9
    i1fd.1
    i1fd.2
    wph
    @35
    @36
    cvol
    cfv
    #
    cr
    wcel
    #
    wi
    #
    vy
    wal
    cc0
    @6
    wcel
    #
    wn
    #
    @9
    wph
    @77
    vy
    wph
    @35
    @76
    @42
    @75
    @36
    covol
    cfv
    #
    cr
    @42
    @37
    @75
    @80
    wceq
    @68
    @36
    mblvol
    syl
    @42
    @36
    cr
    wss
    #
    @43
    @45
    covol
    cfv
    #
    vx
    csu
    #
    cr
    wcel
    @80
    @83
    cle
    wbr
    @80
    cr
    wcel
    @42
    @37
    @81
    @68
    @36
    mblss
    syl
    @42
    @43
    @82
    vx
    @56
    @58
    @45
    cvol
    cfv
    #
    @82
    cr
    @58
    @53
    @84
    @82
    wceq
    @67
    @45
    mblvol
    syl
    @58
    wph
    @60
    @84
    cr
    wcel
    @61
    @66
    i1fd.4
    syl2anc
    eqeltrrd
    #
    fsumrecl
    @42
    @46
    covol
    cfv
    #
    @80
    @83
    cle
    @42
    @46
    @36
    covol
    @51
    fveq2d
    @42
    @52
    @45
    cr
    wss
    #
    @82
    cr
    wcel
    #
    wa
    #
    vx
    @43
    wral
    @86
    @83
    cle
    wbr
    @56
    @42
    @89
    vx
    @43
    @58
    @87
    @88
    @58
    @53
    @87
    @67
    @45
    mblss
    syl
    @85
    jca
    ralrimiva
    @43
    @45
    vx
    ovolfiniun
    syl2anc
    eqbrtrrd
    @36
    @83
    ovollecl
    syl3anc
    eqeltrd
    ex
    alrimiv
    cc0
    cr
    neldifsn
    @77
    @79
    @9
    wi
    vy
    @6
    @70
    @6
    cvv
    wcel
    reex
    cr
    @5
    cvv
    difexg
    ax-mp
    @33
    @6
    wceq
    #
    @35
    @79
    @76
    @9
    @90
    @34
    @78
    @33
    @6
    cc0
    eleq2
    notbid
    @90
    @75
    @8
    cr
    @90
    @36
    @7
    cvol
    @33
    @6
    @4
    imaeq2
    fveq2d
    eleq1d
    imbi12d
    spcv
    mpisyl
    3jca
    cF
    isi1f
    sylanbrc
end

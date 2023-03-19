include "cmul.mm"
include "cof.mm"
include "co.mm"
include "cr.mm"
include "cvv.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "remulcl.mm"
include "adantl.mm"
include "citg1.mm"
include "cdm.mm"
include "wf.mm"
include "i1ff.mm"
include "syl.mm"
include "reex.mm"
include "a1i.mm"
include "inidm.mm"
include "off.mm"
include "crn.mm"
include "cmpt2.mm"
include "cfn.mm"
include "wss.mm"
include "cxp.mm"
include "wfo.mm"
include "i1frn.mm"
include "xpfi.mm"
include "syl2anc.mm"
include "wfn.mm"
include "eqid.mm"
include "ovex.mm"
include "fnmpt2i.mm"
include "dffn4.mm"
include "mpbi.mm"
include "fofi.mm"
include "sylancl.mm"
include "wceq.mm"
include "wrex.mm"
include "cab.mm"
include "rspceov.mm"
include "mp3an3.mm"
include "eqeq1.mm"
include "2rexbidv.mm"
include "elab.mm"
include "sylibr.mm"
include "ffn.mm"
include "dffn3.mm"
include "sylib.mm"
include "frn.mm"
include "rnmpt2.mm"
include "syl6sseqr.mm"
include "ssfi.mm"
include "cc0.mm"
include "csn.mm"
include "cdif.mm"
include "ccnv.mm"
include "cima.mm"
include "cdiv.mm"
include "cin.mm"
include "ciun.mm"
include "cvol.mm"
include "cc.mm"
include "ax-resscn.mm"
include "syl6ss.mm"
include "ssdifd.mm"
include "sselda.mm"
include "i1fmullem.mm"
include "syldan.mm"
include "wral.mm"
include "difss.mm"
include "i1fima.mm"
include "inmbl.mm"
include "ralrimivw.mm"
include "finiunmbl.mm"
include "adantr.mm"
include "eqeltrd.mm"
include "cfv.mm"
include "covol.mm"
include "mblvol.mm"
include "csu.mm"
include "cle.mm"
include "wbr.mm"
include "mblss.mm"
include "inss2.mm"
include "ad2antrr.mm"
include "i1fima2sn.mm"
include "sylan.mm"
include "eqeltrrd.mm"
include "ovolsscl.mm"
include "syl3anc.mm"
include "fsumrecl.mm"
include "fveq2d.mm"
include "jca.mm"
include "ralrimiva.mm"
include "ovolfiniun.mm"
include "eqbrtrd.mm"
include "ovollecl.mm"
include "i1fd.mm"

theorem i1fmul
  let wph: wff ph
  let cF: class F
  let cG: class G
  let vi: setvar i
  let vj: setvar j
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let vw: setvar w
  let cI: class I
  let vv: setvar v
  let vx: setvar x
  let cP: class P
  let vu: setvar u
  assume i1fadd.1: |- ( ph -> F e. dom S.1 )
  assume i1fadd.2: |- ( ph -> G e. dom S.1 )


  assert |- ( ph -> ( F oF x. G ) e. dom S.1 )

  proof
    wph
    vy
    cF
    cG
    cmul
    cof
    co
    #
    wph
    vx
    vy
    cr
    cr
    cr
    cmul
    cr
    cr
    cr
    cF
    cG
    cvv
    cvv
    vx
    cv
    #
    cr
    wcel
    vy
    cv
    #
    cr
    wcel
    wa
    @1
    @2
    cmul
    co
    #
    cr
    wcel
    wph
    @1
    @2
    remulcl
    adantl
    wph
    cF
    citg1
    cdm
    #
    wcel
    #
    cr
    cr
    cF
    wf
    #
    i1fadd.1
    cF
    i1ff
    syl
    #
    wph
    cG
    @4
    wcel
    #
    cr
    cr
    cG
    wf
    #
    i1fadd.2
    cG
    i1ff
    syl
    #
    cr
    cvv
    wcel
    wph
    reex
    a1i
    #
    @11
    cr
    inidm
    #
    off
    #
    wph
    vu
    vv
    cF
    crn
    #
    cG
    crn
    #
    vu
    cv
    #
    vv
    cv
    #
    cmul
    co
    #
    cmpt2
    #
    crn
    #
    cfn
    wcel
    #
    @0
    crn
    #
    @20
    wss
    @22
    cfn
    wcel
    wph
    @14
    @15
    cxp
    #
    cfn
    wcel
    #
    @23
    @20
    @19
    wfo
    #
    @21
    wph
    @14
    cfn
    wcel
    #
    @15
    cfn
    wcel
    #
    @24
    wph
    @5
    @26
    i1fadd.1
    cF
    i1frn
    syl
    wph
    @8
    @27
    i1fadd.2
    cG
    i1frn
    syl
    #
    @14
    @15
    xpfi
    syl2anc
    @19
    @23
    wfn
    @25
    vu
    vv
    @14
    @15
    @18
    @19
    @19
    eqid
    #
    @16
    @17
    cmul
    ovex
    fnmpt2i
    @23
    @19
    dffn4
    mpbi
    @23
    @20
    @19
    fofi
    sylancl
    wph
    @22
    vw
    cv
    #
    @18
    wceq
    #
    vv
    @15
    wrex
    vu
    @14
    wrex
    #
    vw
    cab
    #
    @20
    wph
    cr
    @33
    @0
    wf
    @22
    @33
    wss
    wph
    vx
    vy
    cr
    cr
    cr
    cmul
    @14
    @15
    @33
    cF
    cG
    cvv
    cvv
    @1
    @14
    wcel
    #
    @2
    @15
    wcel
    #
    wa
    #
    @3
    @33
    wcel
    #
    wph
    @36
    @3
    @18
    wceq
    #
    vv
    @15
    wrex
    vu
    @14
    wrex
    #
    @37
    @34
    @35
    @3
    @3
    wceq
    @39
    @3
    eqid
    vu
    vv
    @14
    @15
    @1
    @2
    @3
    cmul
    rspceov
    mp3an3
    @32
    @39
    vw
    @3
    @1
    @2
    cmul
    ovex
    @30
    @3
    wceq
    @31
    @38
    vu
    vv
    @14
    @15
    @30
    @3
    @18
    eqeq1
    2rexbidv
    elab
    sylibr
    adantl
    wph
    cF
    cr
    wfn
    #
    cr
    @14
    cF
    wf
    wph
    @6
    @40
    @7
    cr
    cr
    cF
    ffn
    syl
    cr
    cF
    dffn3
    sylib
    wph
    cG
    cr
    wfn
    #
    cr
    @15
    cG
    wf
    wph
    @9
    @41
    @10
    cr
    cr
    cG
    ffn
    syl
    cr
    cG
    dffn3
    sylib
    @11
    @11
    @12
    off
    cr
    @33
    @0
    frn
    syl
    vu
    vv
    vw
    @14
    @15
    @18
    @19
    @29
    rnmpt2
    syl6sseqr
    @20
    @22
    ssfi
    syl2anc
    wph
    @2
    @22
    cc0
    csn
    #
    cdif
    #
    wcel
    #
    wa
    #
    @0
    ccnv
    @2
    csn
    cima
    #
    vz
    @15
    @42
    cdif
    #
    cF
    ccnv
    @2
    vz
    cv
    #
    cdiv
    co
    csn
    #
    cima
    #
    cG
    ccnv
    @48
    csn
    #
    cima
    #
    cin
    #
    ciun
    #
    cvol
    cdm
    #
    wph
    @44
    @2
    cc
    @42
    cdif
    #
    wcel
    @46
    @54
    wceq
    wph
    @43
    @56
    @2
    wph
    @22
    cc
    @42
    wph
    @22
    cr
    cc
    wph
    cr
    cr
    @0
    wf
    @22
    cr
    wss
    @13
    cr
    cr
    @0
    frn
    syl
    ax-resscn
    syl6ss
    ssdifd
    sselda
    wph
    vz
    @2
    cF
    cG
    i1fadd.1
    i1fadd.2
    i1fmullem
    syldan
    #
    wph
    @54
    @55
    wcel
    #
    @44
    wph
    @47
    cfn
    wcel
    #
    @53
    @55
    wcel
    #
    vz
    @47
    wral
    @58
    wph
    @27
    @47
    @15
    wss
    @59
    @28
    @15
    @42
    difss
    @15
    @47
    ssfi
    sylancl
    #
    wph
    @60
    vz
    @47
    wph
    @50
    @55
    wcel
    #
    @52
    @55
    wcel
    #
    @60
    wph
    @5
    @62
    i1fadd.1
    @49
    cF
    i1fima
    syl
    wph
    @8
    @63
    i1fadd.2
    @51
    cG
    i1fima
    syl
    #
    @50
    @52
    inmbl
    syl2anc
    #
    ralrimivw
    @47
    @53
    vz
    finiunmbl
    syl2anc
    adantr
    eqeltrd
    #
    @45
    @46
    cvol
    cfv
    #
    @46
    covol
    cfv
    #
    cr
    @45
    @46
    @55
    wcel
    #
    @67
    @68
    wceq
    @66
    @46
    mblvol
    syl
    @45
    @46
    cr
    wss
    #
    @47
    @53
    covol
    cfv
    #
    vz
    csu
    #
    cr
    wcel
    @68
    @72
    cle
    wbr
    @68
    cr
    wcel
    @45
    @69
    @70
    @66
    @46
    mblss
    syl
    @45
    @47
    @71
    vz
    wph
    @59
    @44
    @61
    adantr
    #
    @45
    @48
    @47
    wcel
    #
    wa
    #
    @53
    @52
    wss
    #
    @52
    cr
    wss
    #
    @52
    covol
    cfv
    #
    cr
    wcel
    @71
    cr
    wcel
    #
    @76
    @75
    @50
    @52
    inss2
    a1i
    @75
    @63
    @77
    wph
    @63
    @44
    @74
    @64
    ad2antrr
    #
    @52
    mblss
    syl
    @75
    @52
    cvol
    cfv
    #
    @78
    cr
    @75
    @63
    @81
    @78
    wceq
    @80
    @52
    mblvol
    syl
    @45
    @8
    @74
    @81
    cr
    wcel
    wph
    @8
    @44
    i1fadd.2
    adantr
    @48
    @15
    cG
    i1fima2sn
    sylan
    eqeltrrd
    @53
    @52
    ovolsscl
    syl3anc
    #
    fsumrecl
    @45
    @68
    @54
    covol
    cfv
    #
    @72
    cle
    @45
    @46
    @54
    covol
    @57
    fveq2d
    @45
    @59
    @53
    cr
    wss
    #
    @79
    wa
    #
    vz
    @47
    wral
    @83
    @72
    cle
    wbr
    @73
    @45
    @85
    vz
    @47
    @75
    @84
    @79
    wph
    @84
    @44
    @74
    wph
    @60
    @84
    @65
    @53
    mblss
    syl
    ad2antrr
    @82
    jca
    ralrimiva
    @47
    @53
    vz
    ovolfiniun
    syl2anc
    eqbrtrd
    @46
    @72
    ovollecl
    syl3anc
    eqeltrd
    i1fd
end

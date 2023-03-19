include "cioo.mm"
include "ccom.mm"
include "crn.mm"
include "cuni.mm"
include "cicc.mm"
include "wss.mm"
include "cdif.mm"
include "covol.mm"
include "cfv.mm"
include "cc0.mm"
include "wceq.mm"
include "c1st.mm"
include "cima.mm"
include "c2nd.mm"
include "cun.mm"
include "ssun1.mm"
include "cn.mm"
include "cv.mm"
include "ciun.mm"
include "csn.mm"
include "wcel.mm"
include "wa.mm"
include "co.mm"
include "cpr.mm"
include "cr.mm"
include "cle.mm"
include "wbr.mm"
include "w3a.mm"
include "cxp.mm"
include "cin.mm"
include "wf.mm"
include "ovolfcl.mm"
include "sylan.mm"
include "cxr.mm"
include "rexr.mm"
include "id.mm"
include "prunioo.mm"
include "syl3an.mm"
include "syl.mm"
include "fvco3.mm"
include "cop.mm"
include "inss2.mm"
include "ffvelrnda.mm"
include "sseldi.mm"
include "1st2nd2.mm"
include "fveq2d.mm"
include "df-ov.mm"
include "syl6eqr.mm"
include "eqtrd.mm"
include "df-pr.mm"
include "preq12d.mm"
include "syl5eqr.mm"
include "uneq12d.mm"
include "3eqtr4rd.mm"
include "iuneq2dv.mm"
include "wfn.mm"
include "cpw.mm"
include "iccf.mm"
include "ffn.mm"
include "ax-mp.mm"
include "rexpssxrxp.mm"
include "sstri.mm"
include "fss.mm"
include "sylancl.mm"
include "fnfco.mm"
include "sylancr.mm"
include "fniunfv.mm"
include "iunun.mm"
include "ioof.mm"
include "wfun.mm"
include "cdm.mm"
include "cvv.mm"
include "wfo.mm"
include "fo1st.mm"
include "fofn.mm"
include "ssv.mm"
include "fnfun.mm"
include "fndm.mm"
include "eqimss2.mm"
include "3syl.mm"
include "dfimafn2.mm"
include "syl2anc.mm"
include "fnima.mm"
include "eqtr3d.mm"
include "rnco2.mm"
include "syl6eq.mm"
include "fo2nd.mm"
include "syl5eq.mm"
include "3eqtr3d.mm"
include "syl5sseqr.mm"
include "cdom.mm"
include "ovolficcss.mm"
include "ssdifssd.mm"
include "com.mm"
include "cen.mm"
include "ccrd.mm"
include "cres.mm"
include "con0.mm"
include "omelon.mm"
include "nnenom.mm"
include "ensymi.mm"
include "isnumi.mm"
include "mp2an.mm"
include "fofun.mm"
include "fof.mm"
include "fdmi.mm"
include "sseqtr4i.mm"
include "fores.mm"
include "dffn4.mm"
include "sylib.mm"
include "foco.mm"
include "fodomnum.mm"
include "mpsyl.mm"
include "domentr.mm"
include "unctb.mm"
include "reldom.mm"
include "brrelexi.mm"
include "ssid.mm"
include "syl5sseq.mm"
include "ssundif.mm"
include "ssdomg.mm"
include "sylc.mm"
include "domtr.mm"
include "ovolctb2.mm"
include "jca.mm"

theorem uniiccdif
  let wph: wff ph
  let cF: class F
  let va: setvar a
  let vf: setvar f
  let vi: setvar i
  let vj: setvar j
  let vk: setvar k
  let vn: setvar n
  let vr: setvar r
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vm: setvar m
  let vw: setvar w
  let cG: class G
  let cK: class K
  let cA: class A
  let cC: class C
  let cM: class M
  let cE: class E
  let cH: class H
  let cJ: class J
  let cN: class N
  let cS: class S
  let cT: class T
  assume uniioombl.1: |- ( ph -> F : NN --> ( <_ i^i ( RR X. RR ) ) )


  assert |- ( ph -> ( U. ran ( (,) o. F ) C_ U. ran ( [,] o. F ) /\ ( vol* ` ( U. ran ( [,] o. F ) \ U. ran ( (,) o. F ) ) ) = 0 ) )

  proof
    wph
    cioo
    cF
    ccom
    #
    crn
    cuni
    #
    cicc
    cF
    ccom
    #
    crn
    cuni
    #
    wss
    @3
    @1
    cdif
    #
    covol
    cfv
    cc0
    wceq
    #
    wph
    @1
    c1st
    cF
    crn
    #
    cima
    #
    c2nd
    @6
    cima
    #
    cun
    #
    cun
    #
    @1
    @3
    @1
    @9
    ssun1
    wph
    vx
    cn
    vx
    cv
    #
    @2
    cfv
    #
    ciun
    #
    vx
    cn
    @11
    @0
    cfv
    #
    @11
    c1st
    cF
    ccom
    #
    cfv
    #
    csn
    #
    @11
    c2nd
    cF
    ccom
    #
    cfv
    #
    csn
    #
    cun
    #
    cun
    #
    ciun
    #
    @3
    @10
    wph
    vx
    cn
    @12
    @22
    wph
    @11
    cn
    wcel
    #
    wa
    #
    @11
    cF
    cfv
    #
    c1st
    cfv
    #
    @26
    c2nd
    cfv
    #
    cioo
    co
    #
    @27
    @28
    cpr
    #
    cun
    #
    @27
    @28
    cicc
    co
    #
    @22
    @12
    @25
    @27
    cr
    wcel
    #
    @28
    cr
    wcel
    #
    @27
    @28
    cle
    wbr
    #
    w3a
    #
    @31
    @32
    wceq
    #
    wph
    cn
    cle
    cr
    cr
    cxp
    #
    cin
    #
    cF
    wf
    #
    @24
    @36
    uniioombl.1
    cF
    @11
    ovolfcl
    sylan
    @33
    @27
    cxr
    wcel
    @34
    @28
    cxr
    wcel
    @35
    @35
    @37
    @27
    rexr
    @28
    rexr
    @35
    id
    @27
    @28
    prunioo
    syl3an
    syl
    @25
    @14
    @29
    @21
    @30
    @25
    @14
    @26
    cioo
    cfv
    #
    @29
    wph
    @40
    @24
    @14
    @41
    wceq
    uniioombl.1
    cn
    @39
    @11
    cioo
    cF
    fvco3
    sylan
    @25
    @41
    @27
    @28
    cop
    #
    cioo
    cfv
    @29
    @25
    @26
    @42
    cioo
    @25
    @26
    @38
    wcel
    @26
    @42
    wceq
    @25
    @39
    @38
    @26
    cle
    @38
    inss2
    #
    wph
    cn
    @39
    @11
    cF
    uniioombl.1
    ffvelrnda
    sseldi
    @26
    cr
    cr
    1st2nd2
    syl
    #
    fveq2d
    @27
    @28
    cioo
    df-ov
    syl6eqr
    eqtrd
    @25
    @21
    @16
    @19
    cpr
    @30
    @16
    @19
    df-pr
    @25
    @16
    @27
    @19
    @28
    wph
    @40
    @24
    @16
    @27
    wceq
    uniioombl.1
    cn
    @39
    @11
    c1st
    cF
    fvco3
    sylan
    wph
    @40
    @24
    @19
    @28
    wceq
    uniioombl.1
    cn
    @39
    @11
    c2nd
    cF
    fvco3
    sylan
    preq12d
    syl5eqr
    uneq12d
    @25
    @12
    @26
    cicc
    cfv
    #
    @32
    wph
    @40
    @24
    @12
    @45
    wceq
    uniioombl.1
    cn
    @39
    @11
    cicc
    cF
    fvco3
    sylan
    @25
    @45
    @42
    cicc
    cfv
    @32
    @25
    @26
    @42
    cicc
    @44
    fveq2d
    @27
    @28
    cicc
    df-ov
    syl6eqr
    eqtrd
    3eqtr4rd
    iuneq2dv
    wph
    @2
    cn
    wfn
    #
    @13
    @3
    wceq
    wph
    cicc
    cxr
    cxr
    cxp
    #
    wfn
    #
    cn
    @47
    cF
    wf
    #
    @46
    @47
    cxr
    cpw
    #
    cicc
    wf
    @48
    iccf
    @47
    @50
    cicc
    ffn
    ax-mp
    wph
    @40
    @39
    @47
    wss
    @49
    uniioombl.1
    @39
    @38
    @47
    @43
    rexpssxrxp
    sstri
    cn
    @39
    @47
    cF
    fss
    sylancl
    #
    @47
    cn
    cicc
    cF
    fnfco
    sylancr
    vx
    cn
    @2
    fniunfv
    syl
    wph
    @23
    vx
    cn
    @14
    ciun
    #
    vx
    cn
    @21
    ciun
    #
    cun
    @10
    vx
    cn
    @14
    @21
    iunun
    wph
    @52
    @1
    @53
    @9
    wph
    @0
    cn
    wfn
    #
    @52
    @1
    wceq
    wph
    cioo
    @47
    wfn
    #
    @49
    @54
    @47
    cr
    cpw
    #
    cioo
    wf
    @55
    ioof
    @47
    @56
    cioo
    ffn
    ax-mp
    @51
    @47
    cn
    cioo
    cF
    fnfco
    sylancr
    vx
    cn
    @0
    fniunfv
    syl
    wph
    @53
    vx
    cn
    @17
    ciun
    #
    vx
    cn
    @20
    ciun
    #
    cun
    @9
    vx
    cn
    @17
    @20
    iunun
    wph
    @57
    @7
    @58
    @8
    wph
    @57
    @15
    crn
    #
    @7
    wph
    @15
    cn
    cima
    #
    @57
    @59
    wph
    @15
    wfun
    #
    cn
    @15
    cdm
    #
    wss
    #
    @60
    @57
    wceq
    wph
    @15
    cn
    wfn
    #
    @61
    wph
    c1st
    cvv
    wfn
    #
    cn
    cvv
    cF
    wf
    #
    @64
    cvv
    cvv
    c1st
    wfo
    #
    @65
    fo1st
    cvv
    cvv
    c1st
    fofn
    ax-mp
    wph
    @40
    @39
    cvv
    wss
    @66
    uniioombl.1
    @39
    ssv
    cn
    @39
    cvv
    cF
    fss
    sylancl
    #
    cvv
    cn
    c1st
    cF
    fnfco
    sylancr
    #
    cn
    @15
    fnfun
    syl
    wph
    @64
    @62
    cn
    wceq
    @63
    @69
    cn
    @15
    fndm
    cn
    @62
    eqimss2
    3syl
    vx
    cn
    @15
    dfimafn2
    syl2anc
    wph
    @64
    @60
    @59
    wceq
    @69
    cn
    @15
    fnima
    syl
    eqtr3d
    c1st
    cF
    rnco2
    syl6eq
    wph
    @58
    @18
    crn
    #
    @8
    wph
    @18
    cn
    cima
    #
    @58
    @70
    wph
    @18
    wfun
    #
    cn
    @18
    cdm
    #
    wss
    #
    @71
    @58
    wceq
    wph
    @18
    cn
    wfn
    #
    @72
    wph
    c2nd
    cvv
    wfn
    #
    @66
    @75
    cvv
    cvv
    c2nd
    wfo
    #
    @76
    fo2nd
    cvv
    cvv
    c2nd
    fofn
    ax-mp
    @68
    cvv
    cn
    c2nd
    cF
    fnfco
    sylancr
    #
    cn
    @18
    fnfun
    syl
    wph
    @75
    @73
    cn
    wceq
    @74
    @78
    cn
    @18
    fndm
    cn
    @73
    eqimss2
    3syl
    vx
    cn
    @18
    dfimafn2
    syl2anc
    wph
    @75
    @71
    @70
    wceq
    @78
    cn
    @18
    fnima
    syl
    eqtr3d
    c2nd
    cF
    rnco2
    syl6eq
    uneq12d
    syl5eq
    uneq12d
    syl5eq
    3eqtr3d
    #
    syl5sseqr
    wph
    @4
    cr
    wss
    @4
    cn
    cdom
    wbr
    #
    @5
    wph
    @3
    cr
    @1
    wph
    @40
    @3
    cr
    wss
    uniioombl.1
    cF
    ovolficcss
    syl
    ssdifssd
    wph
    @4
    com
    cdom
    wbr
    #
    com
    cn
    cen
    wbr
    #
    @80
    wph
    @4
    @9
    cdom
    wbr
    #
    @9
    com
    cdom
    wbr
    #
    @81
    wph
    @9
    cvv
    wcel
    #
    @4
    @9
    wss
    #
    @83
    wph
    @84
    @85
    wph
    @7
    com
    cdom
    wbr
    #
    @8
    com
    cdom
    wbr
    #
    @84
    wph
    @7
    cn
    cdom
    wbr
    #
    cn
    com
    cen
    wbr
    #
    @87
    cn
    ccrd
    cdm
    wcel
    #
    wph
    cn
    @7
    c1st
    @6
    cres
    #
    cF
    ccom
    #
    wfo
    #
    @89
    com
    con0
    wcel
    @82
    @91
    omelon
    cn
    com
    nnenom
    ensymi
    #
    com
    cn
    isnumi
    mp2an
    #
    wph
    @6
    @7
    @92
    wfo
    #
    cn
    @6
    cF
    wfo
    #
    @94
    c1st
    wfun
    #
    @6
    c1st
    cdm
    #
    wss
    @97
    @67
    @99
    fo1st
    cvv
    cvv
    c1st
    fofun
    ax-mp
    @6
    cvv
    @100
    @6
    ssv
    #
    cvv
    cvv
    c1st
    @67
    cvv
    cvv
    c1st
    wf
    fo1st
    cvv
    cvv
    c1st
    fof
    ax-mp
    fdmi
    sseqtr4i
    @6
    c1st
    fores
    mp2an
    wph
    cF
    cn
    wfn
    #
    @98
    wph
    @40
    @102
    uniioombl.1
    cn
    @39
    cF
    ffn
    syl
    cn
    cF
    dffn4
    sylib
    #
    cn
    @6
    @7
    @92
    cF
    foco
    sylancr
    cn
    @7
    @93
    fodomnum
    mpsyl
    nnenom
    @7
    cn
    com
    domentr
    sylancl
    wph
    @8
    cn
    cdom
    wbr
    #
    @90
    @88
    @91
    wph
    cn
    @8
    c2nd
    @6
    cres
    #
    cF
    ccom
    #
    wfo
    #
    @104
    @96
    wph
    @6
    @8
    @105
    wfo
    #
    @98
    @107
    c2nd
    wfun
    #
    @6
    c2nd
    cdm
    #
    wss
    @108
    @77
    @109
    fo2nd
    cvv
    cvv
    c2nd
    fofun
    ax-mp
    @6
    cvv
    @110
    @101
    cvv
    cvv
    c2nd
    @77
    cvv
    cvv
    c2nd
    wf
    fo2nd
    cvv
    cvv
    c2nd
    fof
    ax-mp
    fdmi
    sseqtr4i
    @6
    c2nd
    fores
    mp2an
    @103
    cn
    @6
    @8
    @105
    cF
    foco
    sylancr
    cn
    @8
    @106
    fodomnum
    mpsyl
    nnenom
    @8
    cn
    com
    domentr
    sylancl
    @7
    @8
    unctb
    syl2anc
    #
    @9
    com
    cdom
    reldom
    brrelexi
    syl
    wph
    @3
    @10
    wss
    @86
    wph
    @3
    @3
    @10
    @3
    ssid
    @79
    syl5sseq
    @3
    @1
    @9
    ssundif
    sylib
    @4
    @9
    cvv
    ssdomg
    sylc
    @111
    @4
    @9
    com
    domtr
    syl2anc
    @95
    @4
    com
    cn
    domentr
    sylancl
    @4
    ovolctb2
    syl2anc
    jca
end

include "clsi.mm"
include "cfv.mm"
include "clsp.mm"
include "cle.mm"
include "wbr.mm"
include "cr.mm"
include "cv.mm"
include "cpnf.mm"
include "cico.mm"
include "co.mm"
include "cima.mm"
include "cxr.mm"
include "cin.mm"
include "clt.mm"
include "cinf.mm"
include "cmpt.mm"
include "crn.mm"
include "csup.mm"
include "wral.mm"
include "wcel.mm"
include "wa.mm"
include "c0.mm"
include "wne.mm"
include "cif.mm"
include "wrex.mm"
include "simpr.mm"
include "simpl.mm"
include "ifcld.mm"
include "adantll.mm"
include "ad2antrr.mm"
include "wceq.mm"
include "oveq1.mm"
include "rexeqdv.mm"
include "rspcva.mm"
include "syl2anc.mm"
include "wss.mm"
include "inss2.mm"
include "infxrcl.mm"
include "ax-mp.mm"
include "a1i.mm"
include "supxrcl.mm"
include "rexr.mm"
include "pnfxr.mm"
include "rexrd.mm"
include "adantr.mm"
include "icossxr.mm"
include "id.mm"
include "sseldi.mm"
include "adantl.mm"
include "max1.mm"
include "icogelbd.mm"
include "xrletrd.mm"
include "icossico2.mm"
include "imass2d.mm"
include "ssrind.mm"
include "infxrss.mm"
include "infxrlesupxr.mm"
include "ad2antlr.mm"
include "max2.mm"
include "supxrss.mm"
include "ad5ant2345.mm"
include "rexlimdva2.mm"
include "mpd.mm"
include "ralrimiva.mm"
include "wb.mm"
include "cvv.mm"
include "nfv.mm"
include "xrltso.mm"
include "supex.mm"
include "breq2.mm"
include "ralrnmpt3.mm"
include "mpbird.mm"
include "imaeq2d.mm"
include "ineq1d.mm"
include "supeq1d.mm"
include "cbvmptv.mm"
include "rneqi.mm"
include "raleqi.mm"
include "mpbid.mm"
include "rgenw.mm"
include "eqid.mm"
include "rnmptss.mm"
include "infxrgelb.mm"
include "nfcv.mm"
include "nfmpt1.mm"
include "nfrn.mm"
include "nfinf.mm"
include "supxrleubrnmptf.mm"
include "liminfvald.mm"
include "limsupvald.mm"
include "breq12d.mm"

theorem liminflelimsuplem
  let wph: wff ph
  let vj: setvar j
  let vk: setvar k
  let cF: class F
  let cV: class V
  let vi: setvar i
  let vl: setvar l
  let vy: setvar y
  let vx: setvar x
  assume liminflelimsuplem.1: |- ( ph -> F e. V )
  assume liminflelimsuplem.2: |- ( ph -> A. k e. RR E. j e. ( k [,) +oo ) ( ( F " ( j [,) +oo ) ) i^i RR* ) =/= (/) )

  disjoint F j
  disjoint F k
  disjoint j k
  disjoint j ph
  disjoint F i
  disjoint F l
  disjoint i j
  disjoint i k
  disjoint i l
  disjoint j l
  disjoint k l
  disjoint F y
  disjoint i y
  disjoint l y
  disjoint i ph
  disjoint l ph
  disjoint k x
  assert |- ( ph -> ( liminf ` F ) <_ ( limsup ` F ) )

  proof
    wph
    cF
    clsi
    cfv
    #
    cF
    clsp
    cfv
    #
    cle
    wbr
    vi
    cr
    cF
    vi
    cv
    #
    cpnf
    cico
    co
    #
    cima
    #
    cxr
    cin
    #
    cxr
    clt
    cinf
    #
    cmpt
    #
    crn
    cxr
    clt
    csup
    #
    vi
    cr
    @5
    cxr
    clt
    csup
    #
    cmpt
    #
    crn
    #
    cxr
    clt
    cinf
    #
    cle
    wbr
    #
    wph
    @13
    @6
    @12
    cle
    wbr
    #
    vi
    cr
    wral
    wph
    @14
    vi
    cr
    wph
    @2
    cr
    wcel
    #
    wa
    #
    @14
    @6
    vy
    cv
    #
    cle
    wbr
    #
    vy
    @11
    wral
    #
    @16
    @18
    vy
    vl
    cr
    cF
    vl
    cv
    #
    cpnf
    cico
    co
    #
    cima
    #
    cxr
    cin
    #
    cxr
    clt
    csup
    #
    cmpt
    #
    crn
    #
    wral
    #
    @19
    @16
    @27
    @6
    @24
    cle
    wbr
    #
    vl
    cr
    wral
    #
    @16
    @28
    vl
    cr
    @16
    @20
    cr
    wcel
    #
    wa
    #
    cF
    vj
    cv
    #
    cpnf
    cico
    co
    #
    cima
    #
    cxr
    cin
    #
    c0
    wne
    #
    vj
    @2
    @20
    cle
    wbr
    #
    @20
    @2
    cif
    #
    cpnf
    cico
    co
    #
    wrex
    #
    @28
    @31
    @38
    cr
    wcel
    #
    @36
    vj
    vk
    cv
    #
    cpnf
    cico
    co
    #
    wrex
    #
    vk
    cr
    wral
    #
    @40
    @15
    @30
    @41
    wph
    @15
    @30
    wa
    #
    @37
    @20
    @2
    cr
    @15
    @30
    simpr
    @15
    @30
    simpl
    ifcld
    #
    adantll
    wph
    @45
    @15
    @30
    liminflelimsuplem.2
    ad2antrr
    @44
    @40
    vk
    @38
    cr
    @42
    @38
    wceq
    @36
    vj
    @43
    @39
    @42
    @38
    cpnf
    cico
    oveq1
    rexeqdv
    rspcva
    syl2anc
    @31
    @36
    @28
    vj
    @39
    @15
    @30
    @32
    @39
    wcel
    #
    @36
    @28
    wph
    @46
    @48
    wa
    #
    @36
    wa
    #
    @6
    @35
    cxr
    clt
    cinf
    #
    @24
    @6
    cxr
    wcel
    #
    @50
    @5
    cxr
    wss
    #
    @52
    @4
    cxr
    inss2
    #
    @5
    infxrcl
    ax-mp
    #
    a1i
    @51
    cxr
    wcel
    #
    @50
    @35
    cxr
    wss
    #
    @56
    @34
    cxr
    inss2
    #
    @35
    infxrcl
    ax-mp
    a1i
    #
    @24
    cxr
    wcel
    #
    @50
    @23
    cxr
    wss
    #
    @60
    @22
    cxr
    inss2
    #
    @23
    supxrcl
    ax-mp
    a1i
    #
    @49
    @6
    @51
    cle
    wbr
    #
    @36
    @49
    @35
    @5
    wss
    @53
    @64
    @49
    @34
    @4
    cxr
    @49
    @33
    @3
    cF
    @49
    @32
    @2
    cpnf
    @15
    @2
    cxr
    wcel
    @30
    @48
    @2
    rexr
    ad2antrr
    #
    cpnf
    cxr
    wcel
    @49
    pnfxr
    a1i
    #
    @49
    @2
    @38
    @32
    @65
    @46
    @38
    cxr
    wcel
    @48
    @46
    @38
    @47
    rexrd
    adantr
    #
    @48
    @32
    cxr
    wcel
    @46
    @48
    @39
    cxr
    @32
    @38
    cpnf
    icossxr
    @48
    id
    sseldi
    adantl
    #
    @46
    @2
    @38
    cle
    wbr
    @48
    @2
    @20
    max1
    adantr
    @49
    @38
    cpnf
    @32
    @67
    @66
    @46
    @48
    simpr
    icogelbd
    #
    xrletrd
    icossico2
    imass2d
    ssrind
    @53
    @49
    @54
    a1i
    @35
    @5
    infxrss
    syl2anc
    adantr
    @50
    @51
    @35
    cxr
    clt
    csup
    #
    @24
    @59
    @70
    cxr
    wcel
    #
    @50
    @57
    @71
    @58
    @35
    supxrcl
    ax-mp
    a1i
    @63
    @50
    @35
    @57
    @50
    @58
    a1i
    @49
    @36
    simpr
    infxrlesupxr
    @49
    @70
    @24
    cle
    wbr
    #
    @36
    @49
    @35
    @23
    wss
    @61
    @72
    @49
    @34
    @22
    cxr
    @49
    @33
    @21
    cF
    @49
    @32
    @20
    cpnf
    @30
    @20
    cxr
    wcel
    @15
    @48
    @20
    rexr
    ad2antlr
    #
    @66
    @49
    @20
    @38
    @32
    @73
    @67
    @68
    @46
    @20
    @38
    cle
    wbr
    @48
    @2
    @20
    max2
    adantr
    @69
    xrletrd
    icossico2
    imass2d
    ssrind
    @61
    @49
    @62
    a1i
    @35
    @23
    supxrss
    syl2anc
    adantr
    xrletrd
    xrletrd
    ad5ant2345
    rexlimdva2
    mpd
    ralrimiva
    wph
    @27
    @29
    wb
    @15
    wph
    @18
    @28
    vl
    vy
    cr
    @24
    cvv
    wph
    vl
    nfv
    @24
    cvv
    wcel
    wph
    @30
    wa
    cxr
    @23
    clt
    xrltso
    supex
    a1i
    @17
    @24
    @6
    cle
    breq2
    ralrnmpt3
    adantr
    mpbird
    @27
    @19
    wb
    @16
    @18
    vy
    @26
    @11
    @25
    @10
    vl
    vi
    cr
    @24
    @9
    @20
    @2
    wceq
    #
    cxr
    @23
    @5
    clt
    @74
    @22
    @4
    cxr
    @74
    @21
    @3
    cF
    @20
    @2
    cpnf
    cico
    oveq1
    imaeq2d
    ineq1d
    supeq1d
    cbvmptv
    rneqi
    raleqi
    a1i
    mpbid
    @16
    @11
    cxr
    wss
    #
    @52
    @14
    @19
    wb
    @75
    @16
    @9
    cxr
    wcel
    #
    vi
    cr
    wral
    @75
    @76
    vi
    cr
    @53
    @76
    @54
    @5
    supxrcl
    ax-mp
    rgenw
    vi
    cr
    @9
    cxr
    @10
    @10
    eqid
    #
    rnmptss
    ax-mp
    #
    a1i
    @52
    @16
    @55
    a1i
    #
    vy
    @11
    @6
    infxrgelb
    syl2anc
    mpbird
    ralrimiva
    wph
    vi
    cr
    @6
    @12
    wph
    vi
    nfv
    vi
    cr
    nfcv
    vi
    @11
    cxr
    clt
    vi
    @10
    vi
    cr
    @9
    nfmpt1
    nfrn
    vi
    cxr
    nfcv
    vi
    clt
    nfcv
    nfinf
    @79
    @12
    cxr
    wcel
    #
    wph
    @75
    @80
    @78
    @11
    infxrcl
    ax-mp
    a1i
    supxrleubrnmptf
    mpbird
    wph
    @0
    @8
    @1
    @12
    cle
    wph
    vi
    cF
    @7
    cV
    liminflelimsuplem.1
    @7
    eqid
    liminfvald
    wph
    vi
    cF
    @10
    cV
    liminflelimsuplem.1
    @77
    limsupvald
    breq12d
    mpbird
end

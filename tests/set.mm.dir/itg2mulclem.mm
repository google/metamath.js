include "cr.mm"
include "csn.mm"
include "cxp.mm"
include "cmul.mm"
include "cof.mm"
include "co.mm"
include "citg2.mm"
include "cfv.mm"
include "cle.mm"
include "wbr.mm"
include "cv.mm"
include "cofr.mm"
include "citg1.mm"
include "wi.mm"
include "cdm.mm"
include "wral.mm"
include "wcel.mm"
include "wa.mm"
include "c1.mm"
include "cdiv.mm"
include "cc0.mm"
include "cpnf.mm"
include "cicc.mm"
include "wf.mm"
include "cico.mm"
include "wss.mm"
include "icossicc.mm"
include "fss.mm"
include "sylancl.mm"
include "adantr.mm"
include "simpr.mm"
include "crp.mm"
include "rpreccld.mm"
include "rpred.mm"
include "i1fmulc.mm"
include "itg2ub.mm"
include "3expia.mm"
include "syl2anc.mm"
include "clt.mm"
include "wb.mm"
include "i1ff.mm"
include "adantl.mm"
include "ffvelrnda.mm"
include "rge0ssre.mm"
include "ad2antrr.mm"
include "rpgt0d.mm"
include "ledivmul.mm"
include "syl112anc.mm"
include "recnd.mm"
include "wne.mm"
include "rpne0d.mm"
include "divrec2d.mm"
include "breq1d.mm"
include "bitr3d.mm"
include "ralbidva.mm"
include "cvv.mm"
include "reex.mm"
include "a1i.mm"
include "ovexd.mm"
include "feqmptd.mm"
include "cmpt.mm"
include "wceq.mm"
include "fconstmpt.mm"
include "offval2.mm"
include "ofrfval2.mm"
include "3bitr4d.mm"
include "itg1mulc.mm"
include "itg1cl.mm"
include "eqtr4d.mm"
include "bitr2d.mm"
include "3imtr4d.mm"
include "ralrimiva.mm"
include "cxr.mm"
include "ge0mulcl.mm"
include "fconstg.mm"
include "syl.mm"
include "rpre.mm"
include "rpge0.mm"
include "elrege0.mm"
include "sylanbrc.mm"
include "snssd.mm"
include "fssd.mm"
include "inidm.mm"
include "off.mm"
include "remulcld.mm"
include "rexrd.mm"
include "itg2leub.mm"
include "mpbird.mm"

theorem itg2mulclem
  let wph: wff ph
  let cA: class A
  let cF: class F
  let vf: setvar f
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume itg2mulc.2: |- ( ph -> F : RR --> ( 0 [,) +oo ) )
  assume itg2mulc.3: |- ( ph -> ( S.2 ` F ) e. RR )
  assume itg2mulclem.4: |- ( ph -> A e. RR+ )


  assert |- ( ph -> ( S.2 ` ( ( RR X. { A } ) oF x. F ) ) <_ ( A x. ( S.2 ` F ) ) )

  proof
    wph
    cr
    cA
    csn
    #
    cxp
    #
    cF
    cmul
    cof
    #
    co
    #
    citg2
    cfv
    cA
    cF
    citg2
    cfv
    #
    cmul
    co
    #
    cle
    wbr
    #
    vf
    cv
    #
    @3
    cle
    cofr
    #
    wbr
    #
    @7
    citg1
    cfv
    #
    @5
    cle
    wbr
    #
    wi
    #
    vf
    citg1
    cdm
    #
    wral
    #
    wph
    @12
    vf
    @13
    wph
    @7
    @13
    wcel
    #
    wa
    #
    cr
    c1
    cA
    cdiv
    co
    #
    csn
    cxp
    #
    @7
    @2
    co
    #
    cF
    @8
    wbr
    #
    @19
    citg1
    cfv
    #
    @4
    cle
    wbr
    #
    @9
    @11
    @16
    cr
    cc0
    cpnf
    cicc
    co
    #
    cF
    wf
    #
    @19
    @13
    wcel
    #
    @20
    @22
    wi
    wph
    @24
    @15
    wph
    cr
    cc0
    cpnf
    cico
    co
    #
    cF
    wf
    #
    @26
    @23
    wss
    #
    @24
    itg2mulc.2
    cc0
    cpnf
    icossicc
    #
    cr
    @26
    @23
    cF
    fss
    sylancl
    adantr
    @16
    @17
    @7
    wph
    @15
    simpr
    #
    @16
    @17
    wph
    @17
    crp
    wcel
    #
    @15
    wph
    cA
    itg2mulclem.4
    rpreccld
    #
    adantr
    rpred
    #
    i1fmulc
    @24
    @25
    @20
    @22
    cF
    @19
    itg2ub
    3expia
    syl2anc
    @16
    vy
    cv
    #
    @7
    cfv
    #
    cA
    @34
    cF
    cfv
    #
    cmul
    co
    #
    cle
    wbr
    #
    vy
    cr
    wral
    @17
    @35
    cmul
    co
    #
    @36
    cle
    wbr
    #
    vy
    cr
    wral
    @9
    @20
    @16
    @38
    @40
    vy
    cr
    @16
    @34
    cr
    wcel
    #
    wa
    #
    @35
    cA
    cdiv
    co
    #
    @36
    cle
    wbr
    #
    @38
    @40
    @42
    @35
    cr
    wcel
    @36
    cr
    wcel
    cA
    cr
    wcel
    #
    cc0
    cA
    clt
    wbr
    #
    @44
    @38
    wb
    @16
    cr
    cr
    @34
    @7
    @15
    cr
    cr
    @7
    wf
    wph
    @7
    i1ff
    adantl
    #
    ffvelrnda
    #
    @16
    cr
    cr
    @34
    cF
    wph
    cr
    cr
    cF
    wf
    #
    @15
    wph
    @27
    @26
    cr
    wss
    @49
    itg2mulc.2
    rge0ssre
    cr
    @26
    cr
    cF
    fss
    sylancl
    adantr
    ffvelrnda
    #
    wph
    @45
    @15
    @41
    wph
    cA
    itg2mulclem.4
    rpred
    #
    ad2antrr
    #
    wph
    @46
    @15
    @41
    wph
    cA
    itg2mulclem.4
    rpgt0d
    #
    ad2antrr
    @35
    @36
    cA
    ledivmul
    syl112anc
    @42
    @43
    @39
    @36
    cle
    @42
    @35
    cA
    @42
    @35
    @48
    recnd
    @42
    cA
    @52
    recnd
    @16
    cA
    cc0
    wne
    @41
    @16
    cA
    wph
    cA
    crp
    wcel
    #
    @15
    itg2mulclem.4
    adantr
    rpne0d
    #
    adantr
    divrec2d
    breq1d
    bitr3d
    ralbidva
    @16
    vy
    cr
    @35
    @37
    cle
    @7
    @3
    cvv
    cr
    cvv
    cr
    cvv
    wcel
    #
    @16
    reex
    a1i
    #
    @48
    @42
    cA
    @36
    cmul
    ovexd
    @16
    vy
    cr
    cr
    @7
    @47
    feqmptd
    #
    @16
    vy
    cr
    cA
    @36
    cmul
    @1
    cF
    cvv
    crp
    cr
    @57
    wph
    @54
    @15
    @41
    itg2mulclem.4
    ad2antrr
    @50
    @1
    vy
    cr
    cA
    cmpt
    wceq
    @16
    vy
    cr
    cA
    fconstmpt
    a1i
    wph
    cF
    vy
    cr
    @36
    cmpt
    wceq
    @15
    wph
    vy
    cr
    @26
    cF
    itg2mulc.2
    feqmptd
    adantr
    #
    offval2
    ofrfval2
    @16
    vy
    cr
    @39
    @36
    cle
    @19
    cF
    cvv
    cvv
    cr
    @57
    @42
    @17
    @35
    cmul
    ovexd
    @50
    @16
    vy
    cr
    @17
    @35
    cmul
    @18
    @7
    cvv
    crp
    cr
    @57
    wph
    @31
    @15
    @41
    @32
    ad2antrr
    @48
    @18
    vy
    cr
    @17
    cmpt
    wceq
    @16
    vy
    cr
    @17
    fconstmpt
    a1i
    @58
    offval2
    @59
    ofrfval2
    3bitr4d
    @16
    @22
    @10
    cA
    cdiv
    co
    #
    @4
    cle
    wbr
    #
    @11
    @16
    @21
    @60
    @4
    cle
    @16
    @21
    @17
    @10
    cmul
    co
    @60
    @16
    @17
    @7
    @30
    @33
    itg1mulc
    @16
    @10
    cA
    @16
    @10
    @15
    @10
    cr
    wcel
    #
    wph
    @7
    itg1cl
    adantl
    #
    recnd
    @16
    cA
    wph
    @45
    @15
    @51
    adantr
    #
    recnd
    @55
    divrec2d
    eqtr4d
    breq1d
    @16
    @62
    @4
    cr
    wcel
    #
    @45
    @46
    @61
    @11
    wb
    @63
    wph
    @65
    @15
    itg2mulc.3
    adantr
    @64
    wph
    @46
    @15
    @53
    adantr
    @10
    @4
    cA
    ledivmul
    syl112anc
    bitr2d
    3imtr4d
    ralrimiva
    wph
    cr
    @23
    @3
    wf
    #
    @5
    cxr
    wcel
    @6
    @14
    wb
    wph
    cr
    @26
    @3
    wf
    @28
    @66
    wph
    vx
    vy
    cr
    cr
    cr
    cmul
    @26
    @26
    @26
    @1
    cF
    cvv
    cvv
    vx
    cv
    #
    @26
    wcel
    @34
    @26
    wcel
    wa
    @67
    @34
    cmul
    co
    @26
    wcel
    wph
    @67
    @34
    ge0mulcl
    adantl
    wph
    cr
    @0
    @26
    @1
    wph
    @54
    cr
    @0
    @1
    wf
    itg2mulclem.4
    cr
    cA
    crp
    fconstg
    syl
    wph
    cA
    @26
    wph
    @54
    cA
    @26
    wcel
    #
    itg2mulclem.4
    @54
    @45
    cc0
    cA
    cle
    wbr
    @68
    cA
    rpre
    cA
    rpge0
    cA
    elrege0
    sylanbrc
    syl
    snssd
    fssd
    itg2mulc.2
    @56
    wph
    reex
    a1i
    #
    @69
    cr
    inidm
    off
    @29
    cr
    @26
    @23
    @3
    fss
    sylancl
    wph
    @5
    wph
    cA
    @4
    @51
    itg2mulc.3
    remulcld
    rexrd
    @5
    vf
    @3
    itg2leub
    syl2anc
    mpbird
end

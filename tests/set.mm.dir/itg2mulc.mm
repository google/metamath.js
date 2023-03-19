include "cc0.mm"
include "clt.mm"
include "wbr.mm"
include "cr.mm"
include "csn.mm"
include "cxp.mm"
include "cmul.mm"
include "cof.mm"
include "co.mm"
include "citg2.mm"
include "cfv.mm"
include "wceq.mm"
include "wa.mm"
include "cle.mm"
include "cpnf.mm"
include "cico.mm"
include "wf.mm"
include "adantr.mm"
include "wcel.mm"
include "crp.mm"
include "elrege0.mm"
include "sylib.mm"
include "simpld.mm"
include "anim1i.mm"
include "elrp.mm"
include "sylibr.mm"
include "itg2mulclem.mm"
include "cdiv.mm"
include "c1.mm"
include "cvv.mm"
include "cv.mm"
include "ge0mulcl.mm"
include "adantl.mm"
include "fconst6g.mm"
include "syl.mm"
include "reex.mm"
include "a1i.mm"
include "inidm.mm"
include "off.mm"
include "cicc.mm"
include "wss.mm"
include "icossicc.mm"
include "fss.mm"
include "sylancl.mm"
include "remulcld.mm"
include "itg2lecl.mm"
include "syl3anc.mm"
include "rpreccld.mm"
include "cmpt.mm"
include "feqmptd.mm"
include "cc.mm"
include "rge0ssre.mm"
include "ax-resscn.mm"
include "sstri.mm"
include "ffvelrnda.mm"
include "mulid2d.mm"
include "mpteq2dva.mm"
include "eqtr4d.mm"
include "1red.mm"
include "ofc12.mm"
include "fconstmpt.mm"
include "syl6eq.mm"
include "recnd.mm"
include "rpne0d.mm"
include "recid2d.mm"
include "mpteq2dv.mm"
include "eqtrd.mm"
include "offval2.mm"
include "rpcnd.mm"
include "w3a.mm"
include "mulass.mm"
include "caofass.mm"
include "3eqtr2d.mm"
include "fveq2d.mm"
include "divrec2d.mm"
include "3brtr4d.mm"
include "lemuldiv2d.mm"
include "mpbird.mm"
include "wb.mm"
include "cxr.mm"
include "itg2cl.mm"
include "rexrd.mm"
include "xrletri3.mm"
include "syl2anc.mm"
include "mpbir2and.mm"
include "0re.mm"
include "simplr.mm"
include "oveq1d.mm"
include "mul02.mm"
include "eqtr3d.mm"
include "caofid2.mm"
include "itg20.mm"
include "mul02d.mm"
include "simpr.mm"
include "wo.mm"
include "simprd.mm"
include "leloe.mm"
include "sylancr.mm"
include "mpbid.mm"
include "mpjaodan.mm"

theorem itg2mulc
  let wph: wff ph
  let cA: class A
  let cF: class F
  let vf: setvar f
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume itg2mulc.2: |- ( ph -> F : RR --> ( 0 [,) +oo ) )
  assume itg2mulc.3: |- ( ph -> ( S.2 ` F ) e. RR )
  assume itg2mulc.4: |- ( ph -> A e. ( 0 [,) +oo ) )


  assert |- ( ph -> ( S.2 ` ( ( RR X. { A } ) oF x. F ) ) = ( A x. ( S.2 ` F ) ) )

  proof
    wph
    cc0
    cA
    clt
    wbr
    #
    cr
    cA
    csn
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
    #
    cA
    cF
    citg2
    cfv
    #
    cmul
    co
    #
    wceq
    #
    cc0
    cA
    wceq
    #
    wph
    @0
    wa
    #
    @7
    @4
    @6
    cle
    wbr
    #
    @6
    @4
    cle
    wbr
    #
    @9
    cA
    cF
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
    @0
    itg2mulc.2
    adantr
    #
    wph
    @5
    cr
    wcel
    #
    @0
    itg2mulc.3
    adantr
    #
    @9
    cA
    cr
    wcel
    #
    @0
    wa
    cA
    crp
    wcel
    wph
    @17
    @0
    wph
    @17
    cc0
    cA
    cle
    wbr
    #
    wph
    cA
    @12
    wcel
    #
    @17
    @18
    wa
    itg2mulc.4
    cA
    elrege0
    sylib
    #
    simpld
    #
    anim1i
    cA
    elrp
    sylibr
    #
    itg2mulclem
    #
    @9
    @11
    @5
    @4
    cA
    cdiv
    co
    #
    cle
    wbr
    @9
    cr
    c1
    cA
    cdiv
    co
    #
    csn
    cxp
    #
    @3
    @2
    co
    #
    citg2
    cfv
    @25
    @4
    cmul
    co
    @5
    @24
    cle
    @9
    @25
    @3
    wph
    cr
    @12
    @3
    wf
    #
    @0
    wph
    vx
    vy
    cr
    cr
    cr
    cmul
    @12
    @12
    @12
    @1
    cF
    cvv
    cvv
    vx
    cv
    #
    @12
    wcel
    vy
    cv
    #
    @12
    wcel
    wa
    @29
    @30
    cmul
    co
    #
    @12
    wcel
    wph
    @29
    @30
    ge0mulcl
    adantl
    wph
    @19
    cr
    @12
    @1
    wf
    itg2mulc.4
    cr
    cA
    @12
    fconst6g
    syl
    itg2mulc.2
    cr
    cvv
    wcel
    #
    wph
    reex
    a1i
    #
    @33
    cr
    inidm
    off
    #
    adantr
    @9
    cr
    cc0
    cpnf
    cicc
    co
    #
    @3
    wf
    #
    @6
    cr
    wcel
    #
    @10
    @4
    cr
    wcel
    wph
    @36
    @0
    wph
    @28
    @12
    @35
    wss
    @36
    @34
    cc0
    cpnf
    icossicc
    cr
    @12
    @35
    @3
    fss
    sylancl
    #
    adantr
    wph
    @37
    @0
    wph
    cA
    @5
    @21
    itg2mulc.3
    remulcld
    #
    adantr
    @23
    @6
    @3
    itg2lecl
    syl3anc
    #
    @9
    cA
    @22
    rpreccld
    #
    itg2mulclem
    @9
    cF
    @27
    citg2
    @9
    cF
    vy
    cr
    c1
    @30
    cF
    cfv
    #
    cmul
    co
    #
    cmpt
    #
    @26
    @1
    @2
    co
    #
    cF
    @2
    co
    @27
    @9
    cF
    vy
    cr
    @42
    cmpt
    @44
    @9
    vy
    cr
    @12
    cF
    @14
    feqmptd
    #
    @9
    vy
    cr
    @43
    @42
    @9
    @30
    cr
    wcel
    wa
    #
    @42
    @9
    cr
    cc
    @30
    cF
    wph
    cr
    cc
    cF
    wf
    #
    @0
    wph
    @13
    @12
    cc
    wss
    @48
    itg2mulc.2
    @12
    cr
    cc
    rge0ssre
    ax-resscn
    sstri
    cr
    @12
    cc
    cF
    fss
    sylancl
    #
    adantr
    #
    ffvelrnda
    #
    mulid2d
    mpteq2dva
    eqtr4d
    @9
    vy
    cr
    c1
    @42
    cmul
    @45
    cF
    cvv
    cr
    cc
    @32
    @9
    reex
    a1i
    #
    @47
    1red
    @51
    @9
    @45
    vy
    cr
    @25
    cA
    cmul
    co
    #
    cmpt
    #
    vy
    cr
    c1
    cmpt
    @9
    @45
    cr
    @53
    csn
    cxp
    @54
    @9
    cr
    @25
    cA
    cmul
    cvv
    crp
    crp
    @52
    @41
    @22
    ofc12
    vy
    cr
    @53
    fconstmpt
    syl6eq
    @9
    vy
    cr
    @53
    c1
    @9
    cA
    wph
    cA
    cc
    wcel
    #
    @0
    wph
    cA
    @21
    recnd
    adantr
    #
    @9
    cA
    @22
    rpne0d
    #
    recid2d
    mpteq2dv
    eqtrd
    @46
    offval2
    @9
    vx
    vy
    vz
    cr
    cmul
    cmul
    cc
    cmul
    @26
    @1
    cF
    cmul
    cvv
    @52
    @9
    @25
    cc
    wcel
    cr
    cc
    @26
    wf
    @9
    @25
    @41
    rpcnd
    cr
    @25
    cc
    fconst6g
    syl
    @9
    @55
    cr
    cc
    @1
    wf
    @56
    cr
    cA
    cc
    fconst6g
    syl
    @50
    @29
    cc
    wcel
    #
    @30
    cc
    wcel
    vz
    cv
    #
    cc
    wcel
    w3a
    @31
    @59
    cmul
    co
    @29
    @30
    @59
    cmul
    co
    cmul
    co
    wceq
    @9
    @29
    @30
    @59
    mulass
    adantl
    caofass
    3eqtr2d
    fveq2d
    @9
    @4
    cA
    @9
    @4
    @40
    recnd
    @56
    @57
    divrec2d
    3brtr4d
    @9
    @5
    @4
    cA
    @16
    @40
    @22
    lemuldiv2d
    mpbird
    wph
    @7
    @10
    @11
    wa
    wb
    #
    @0
    wph
    @4
    cxr
    wcel
    #
    @6
    cxr
    wcel
    @60
    wph
    @36
    @61
    @38
    @3
    itg2cl
    syl
    wph
    @6
    @39
    rexrd
    @4
    @6
    xrletri3
    syl2anc
    adantr
    mpbir2and
    wph
    @8
    wa
    #
    @4
    cc0
    cc0
    @5
    cmul
    co
    @6
    @62
    @4
    cr
    cc0
    csn
    cxp
    #
    citg2
    cfv
    cc0
    @62
    @3
    @63
    citg2
    @62
    vx
    cr
    cA
    cc0
    cmul
    cc
    cF
    cvv
    cr
    cr
    @32
    @62
    reex
    a1i
    wph
    @48
    @8
    @49
    adantr
    wph
    @17
    @8
    @21
    adantr
    cc0
    cr
    wcel
    #
    @62
    0re
    a1i
    @62
    @58
    wa
    #
    cc0
    @29
    cmul
    co
    #
    cA
    @29
    cmul
    co
    cc0
    @65
    cc0
    cA
    @29
    cmul
    wph
    @8
    @58
    simplr
    oveq1d
    @58
    @66
    cc0
    wceq
    @62
    @29
    mul02
    adantl
    eqtr3d
    caofid2
    fveq2d
    itg20
    syl6eq
    @62
    @5
    @62
    @5
    wph
    @15
    @8
    itg2mulc.3
    adantr
    recnd
    mul02d
    @62
    cc0
    cA
    @5
    cmul
    wph
    @8
    simpr
    oveq1d
    3eqtr2d
    wph
    @18
    @0
    @8
    wo
    #
    wph
    @17
    @18
    @20
    simprd
    wph
    @64
    @17
    @18
    @67
    wb
    0re
    @21
    cc0
    cA
    leloe
    sylancr
    mpbid
    mpjaodan
end

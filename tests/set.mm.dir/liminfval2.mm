include "clsi.mm"
include "cfv.mm"
include "crn.mm"
include "cxr.mm"
include "clt.mm"
include "csup.mm"
include "cima.mm"
include "wcel.mm"
include "wceq.mm"
include "cr.mm"
include "cv.mm"
include "cpnf.mm"
include "cico.mm"
include "co.mm"
include "cin.mm"
include "cinf.mm"
include "cmpt.mm"
include "oveq1.mm"
include "imaeq2d.mm"
include "ineq1d.mm"
include "infeq1d.mm"
include "cbvmptv.mm"
include "eqtri.mm"
include "liminfval.mm"
include "syl.mm"
include "cle.mm"
include "wbr.mm"
include "wral.mm"
include "wrex.mm"
include "wss.mm"
include "wb.mm"
include "ssrexr.mm"
include "supxrunb1.mm"
include "mpbird.mm"
include "wa.mm"
include "liminfgf.mm"
include "ffvelrni.mm"
include "ad2antlr.mm"
include "simpll.mm"
include "simprl.mm"
include "sselda.mm"
include "syl2anc.mm"
include "imassrn.mm"
include "wf.mm"
include "frn.mm"
include "ax-mp.mm"
include "sstri.mm"
include "supxrcl.mm"
include "a1i.mm"
include "simplr.mm"
include "simprr.mm"
include "liminfgord.mm"
include "syl3anc.mm"
include "liminfgval.mm"
include "adantlr.mm"
include "breq12d.mm"
include "adantrr.mm"
include "wfn.mm"
include "nfv.mm"
include "inss2.mm"
include "infxrcl.mm"
include "fnmptd.mm"
include "adantr.mm"
include "simpr.mm"
include "fnfvimad.mm"
include "supxrub.mm"
include "xrletrd.mm"
include "rexlimdvaa.mm"
include "ralimdva.mm"
include "mpd.mm"
include "cvv.mm"
include "xrltso.mm"
include "infex.mm"
include "rgenw.mm"
include "fnmpt.mm"
include "breq1.mm"
include "ralrn.mm"
include "sylibr.mm"
include "supxrleub.mm"
include "mp2an.mm"
include "supxrss.mm"
include "xrletri3.mm"
include "sylanbrc.mm"
include "eqtrd.mm"

theorem liminfval2
  let wph: wff ph
  let cA: class A
  let vk: setvar k
  let cF: class F
  let cG: class G
  let cV: class V
  let vn: setvar n
  let vx: setvar x
  let vj: setvar j
  assume liminfval2.1: |- G = ( k e. RR |-> inf ( ( ( F " ( k [,) +oo ) ) i^i RR* ) , RR* , < ) )
  assume liminfval2.2: |- ( ph -> F e. V )
  assume liminfval2.3: |- ( ph -> A C_ RR )
  assume liminfval2.4: |- ( ph -> sup ( A , RR* , < ) = +oo )

  disjoint F k
  disjoint A n
  disjoint A x
  disjoint n x
  disjoint F j
  disjoint j k
  disjoint G n
  disjoint G x
  disjoint j n
  disjoint j ph
  disjoint j x
  disjoint n ph
  disjoint ph x
  disjoint k x
  assert |- ( ph -> ( liminf ` F ) = sup ( ( G " A ) , RR* , < ) )

  proof
    wph
    cF
    clsi
    cfv
    #
    cG
    crn
    #
    cxr
    clt
    csup
    #
    cG
    cA
    cima
    #
    cxr
    clt
    csup
    #
    wph
    cF
    cV
    wcel
    @0
    @2
    wceq
    liminfval2.2
    vj
    cF
    cG
    cV
    cG
    vk
    cr
    cF
    vk
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
    vj
    cr
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
    cxr
    clt
    cinf
    #
    cmpt
    liminfval2.1
    vk
    vj
    cr
    @9
    @14
    @5
    @10
    wceq
    #
    cxr
    @8
    @13
    clt
    @15
    @7
    @12
    cxr
    @15
    @6
    @11
    cF
    @5
    @10
    cpnf
    cico
    oveq1
    imaeq2d
    ineq1d
    infeq1d
    cbvmptv
    eqtri
    #
    liminfval
    syl
    wph
    @2
    @4
    cle
    wbr
    #
    @4
    @2
    cle
    wbr
    #
    @2
    @4
    wceq
    #
    wph
    vx
    cv
    #
    @4
    cle
    wbr
    #
    vx
    @1
    wral
    #
    @17
    wph
    vn
    cv
    #
    cG
    cfv
    #
    @4
    cle
    wbr
    #
    vn
    cr
    wral
    #
    @22
    wph
    @23
    @20
    cle
    wbr
    #
    vx
    cA
    wrex
    #
    vn
    cr
    wral
    #
    @26
    wph
    @29
    cA
    cxr
    clt
    csup
    cpnf
    wceq
    #
    liminfval2.4
    wph
    cA
    cxr
    wss
    @29
    @30
    wb
    wph
    cA
    liminfval2.3
    ssrexr
    vn
    vx
    cA
    supxrunb1
    syl
    mpbird
    wph
    @28
    @25
    vn
    cr
    wph
    @23
    cr
    wcel
    #
    wa
    #
    @27
    @25
    vx
    cA
    @32
    @20
    cA
    wcel
    #
    @27
    wa
    #
    wa
    #
    @24
    @20
    cG
    cfv
    #
    @4
    @31
    @24
    cxr
    wcel
    wph
    @34
    cr
    cxr
    @23
    cG
    vj
    cF
    cG
    @16
    liminfgf
    #
    ffvelrni
    ad2antlr
    @35
    wph
    @33
    @36
    cxr
    wcel
    #
    wph
    @31
    @34
    simpll
    #
    @32
    @33
    @27
    simprl
    #
    wph
    @33
    wa
    #
    @20
    cr
    wcel
    #
    @38
    wph
    cA
    cr
    @20
    liminfval2.3
    sselda
    #
    cr
    cxr
    @20
    cG
    @37
    ffvelrni
    syl
    syl2anc
    @4
    cxr
    wcel
    #
    @35
    @3
    cxr
    wss
    #
    @44
    @3
    @1
    cxr
    cG
    cA
    imassrn
    #
    cr
    cxr
    cG
    wf
    @1
    cxr
    wss
    #
    @37
    cr
    cxr
    cG
    frn
    ax-mp
    #
    sstri
    #
    @3
    supxrcl
    ax-mp
    #
    a1i
    @35
    @24
    @36
    cle
    wbr
    #
    cF
    @23
    cpnf
    cico
    co
    cima
    cxr
    cin
    cxr
    clt
    cinf
    #
    cF
    @20
    cpnf
    cico
    co
    cima
    cxr
    cin
    cxr
    clt
    cinf
    #
    cle
    wbr
    #
    @35
    @31
    @42
    @27
    @54
    wph
    @31
    @34
    simplr
    @35
    wph
    @33
    @42
    @39
    @40
    @43
    syl2anc
    @32
    @33
    @27
    simprr
    @23
    @20
    cF
    liminfgord
    syl3anc
    @32
    @33
    @51
    @54
    wb
    @27
    @32
    @33
    wa
    @24
    @52
    @36
    @53
    cle
    @31
    @24
    @52
    wceq
    wph
    @33
    vj
    cF
    cG
    @23
    @16
    liminfgval
    ad2antlr
    wph
    @33
    @36
    @53
    wceq
    #
    @31
    @41
    @42
    @55
    @43
    vj
    cF
    cG
    @20
    @16
    liminfgval
    syl
    adantlr
    breq12d
    adantrr
    mpbird
    @35
    wph
    @33
    @36
    @4
    cle
    wbr
    #
    @39
    @40
    @41
    @45
    @36
    @3
    wcel
    @56
    @45
    @41
    @49
    a1i
    @41
    cr
    @20
    cA
    cG
    wph
    cG
    cr
    wfn
    #
    @33
    wph
    vj
    cr
    @14
    cG
    cxr
    wph
    vj
    nfv
    @14
    cxr
    wcel
    #
    wph
    @10
    cr
    wcel
    wa
    @13
    cxr
    wss
    @58
    @12
    cxr
    inss2
    @13
    infxrcl
    ax-mp
    a1i
    @16
    fnmptd
    adantr
    @43
    wph
    @33
    simpr
    fnfvimad
    @3
    @36
    supxrub
    syl2anc
    syl2anc
    xrletrd
    rexlimdvaa
    ralimdva
    mpd
    @57
    @22
    @26
    wb
    @14
    cvv
    wcel
    #
    vj
    cr
    wral
    @57
    @59
    vj
    cr
    cxr
    @13
    clt
    xrltso
    infex
    rgenw
    vj
    cr
    @14
    cG
    cvv
    @16
    fnmpt
    ax-mp
    @21
    @25
    vx
    vn
    cr
    cG
    @20
    @24
    @4
    cle
    breq1
    ralrn
    ax-mp
    sylibr
    @47
    @44
    @17
    @22
    wb
    @48
    @50
    vx
    @1
    @4
    supxrleub
    mp2an
    sylibr
    wph
    @3
    @1
    wss
    #
    @47
    @18
    @60
    wph
    @46
    a1i
    @47
    wph
    @48
    a1i
    @3
    @1
    supxrss
    syl2anc
    @2
    cxr
    wcel
    #
    @44
    @19
    @17
    @18
    wa
    wb
    @47
    @61
    @48
    @1
    supxrcl
    ax-mp
    @50
    @2
    @4
    xrletri3
    mp2an
    sylanbrc
    eqtrd
end

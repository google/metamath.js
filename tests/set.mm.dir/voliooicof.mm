include "cvol.mm"
include "cioo.mm"
include "ccom.mm"
include "cico.mm"
include "cc0.mm"
include "cpnf.mm"
include "cicc.mm"
include "co.mm"
include "wf.mm"
include "wfn.mm"
include "cxr.mm"
include "cxp.mm"
include "cr.mm"
include "volioof.mm"
include "a1i.mm"
include "wss.mm"
include "rexpssxrxp.mm"
include "fcoss.mm"
include "ffn.mm"
include "syl.mm"
include "cdm.mm"
include "volf.mm"
include "cv.mm"
include "cfv.mm"
include "wcel.mm"
include "wral.mm"
include "wa.mm"
include "cpw.mm"
include "icof.mm"
include "c1st.mm"
include "c2nd.mm"
include "adantr.mm"
include "simpr.mm"
include "fvovco.mm"
include "ffvelrnda.mm"
include "xp1st.mm"
include "xp2nd.mm"
include "rexrd.mm"
include "icombl.mm"
include "syl2anc.mm"
include "eqeltrd.mm"
include "ralrimiva.mm"
include "jca.mm"
include "ffnfv.mm"
include "sylibr.mm"
include "fco.mm"
include "wceq.mm"
include "coass.mm"
include "feq1d.mm"
include "mpbird.mm"
include "voliooico.mm"
include "fssd.mm"
include "fvvolioof.mm"
include "fvvolicof.mm"
include "3eqtr4d.mm"
include "eqfnfvd.mm"

theorem voliooicof
  let wph: wff ph
  let cA: class A
  let cF: class F
  let vx: setvar x
  let vk: setvar k
  assume voliooicof.1: |- ( ph -> F : A --> ( RR X. RR ) )


  assert |- ( ph -> ( ( vol o. (,) ) o. F ) = ( ( vol o. [,) ) o. F ) )

  proof
    wph
    vx
    cA
    cvol
    cioo
    ccom
    #
    cF
    ccom
    #
    cvol
    cico
    ccom
    cF
    ccom
    #
    wph
    cA
    cc0
    cpnf
    cicc
    co
    #
    @1
    wf
    @1
    cA
    wfn
    wph
    cxr
    cxr
    cxp
    #
    @3
    cr
    cr
    cxp
    #
    cA
    @0
    cF
    @4
    @3
    @0
    wf
    wph
    volioof
    a1i
    @5
    @4
    wss
    wph
    rexpssxrxp
    a1i
    #
    voliooicof.1
    fcoss
    cA
    @3
    @1
    ffn
    syl
    wph
    cA
    @3
    @2
    wf
    #
    @2
    cA
    wfn
    wph
    @7
    cA
    @3
    cvol
    cico
    cF
    ccom
    #
    ccom
    #
    wf
    #
    wph
    cvol
    cdm
    #
    @3
    cvol
    wf
    #
    cA
    @11
    @8
    wf
    #
    @10
    @12
    wph
    volf
    a1i
    wph
    @8
    cA
    wfn
    #
    vx
    cv
    #
    @8
    cfv
    #
    @11
    wcel
    #
    vx
    cA
    wral
    #
    wa
    @13
    wph
    @14
    @18
    wph
    cA
    cxr
    cpw
    #
    @8
    wf
    @14
    wph
    @4
    @19
    @5
    cA
    cico
    cF
    @4
    @19
    cico
    wf
    wph
    icof
    a1i
    @6
    voliooicof.1
    fcoss
    cA
    @19
    @8
    ffn
    syl
    wph
    @17
    vx
    cA
    wph
    @15
    cA
    wcel
    #
    wa
    #
    @16
    @15
    cF
    cfv
    #
    c1st
    cfv
    #
    @22
    c2nd
    cfv
    #
    cico
    co
    #
    @11
    @21
    cF
    cico
    cr
    cr
    cA
    @15
    wph
    cA
    @5
    cF
    wf
    @20
    voliooicof.1
    adantr
    wph
    @20
    simpr
    #
    fvovco
    @21
    @23
    cr
    wcel
    #
    @24
    cxr
    wcel
    @25
    @11
    wcel
    @21
    @22
    @5
    wcel
    #
    @27
    wph
    cA
    @5
    @15
    cF
    voliooicof.1
    ffvelrnda
    #
    @22
    cr
    cr
    xp1st
    syl
    #
    @21
    @24
    @21
    @28
    @24
    cr
    wcel
    @29
    @22
    cr
    cr
    xp2nd
    syl
    #
    rexrd
    @23
    @24
    icombl
    syl2anc
    eqeltrd
    ralrimiva
    jca
    vx
    cA
    @11
    @8
    ffnfv
    sylibr
    cA
    @11
    @3
    cvol
    @8
    fco
    syl2anc
    wph
    cA
    @3
    @2
    @9
    @2
    @9
    wceq
    wph
    cvol
    cico
    cF
    coass
    a1i
    feq1d
    mpbird
    cA
    @3
    @2
    ffn
    syl
    @21
    @23
    @24
    cioo
    co
    cvol
    cfv
    @25
    cvol
    cfv
    @15
    @1
    cfv
    @15
    @2
    cfv
    @21
    @23
    @24
    @30
    @31
    voliooico
    @21
    cA
    cF
    @15
    wph
    cA
    @4
    cF
    wf
    @20
    wph
    cA
    @5
    @4
    cF
    voliooicof.1
    @6
    fssd
    adantr
    #
    @26
    fvvolioof
    @21
    cA
    cF
    @15
    @32
    @26
    fvvolicof
    3eqtr4d
    eqfnfvd
end

include "cc0.mm"
include "cpnf.mm"
include "cicc.mm"
include "co.mm"
include "cvol.mm"
include "cico.mm"
include "ccom.mm"
include "wf.mm"
include "cdm.mm"
include "crn.mm"
include "volf.mm"
include "a1i.mm"
include "wfn.mm"
include "cv.mm"
include "cfv.mm"
include "wcel.mm"
include "wral.mm"
include "wss.mm"
include "cxr.mm"
include "cpw.mm"
include "cxp.mm"
include "cr.mm"
include "icof.mm"
include "ressxr.mm"
include "xpss1.mm"
include "ax-mp.mm"
include "fcoss.mm"
include "ffnd.mm"
include "wa.mm"
include "c1st.mm"
include "c2nd.mm"
include "adantr.mm"
include "simpr.mm"
include "fvovco.mm"
include "ffvelrnda.mm"
include "xp1st.mm"
include "syl.mm"
include "xp2nd.mm"
include "icombl.mm"
include "syl2anc.mm"
include "eqeltrd.mm"
include "ralrimiva.mm"
include "fnfvrnss.mm"
include "ffrn.mm"
include "wb.mm"
include "coass.mm"
include "feq1i.mm"
include "mpbird.mm"

theorem volicoff
  let wph: wff ph
  let cA: class A
  let cF: class F
  let vx: setvar x
  let vk: setvar k
  assume volicoff.1: |- ( ph -> F : A --> ( RR X. RR* ) )


  assert |- ( ph -> ( ( vol o. [,) ) o. F ) : A --> ( 0 [,] +oo ) )

  proof
    wph
    cA
    cc0
    cpnf
    cicc
    co
    #
    cvol
    cico
    ccom
    cF
    ccom
    #
    wf
    #
    cA
    @0
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
    @0
    @3
    crn
    #
    cA
    cvol
    @3
    @6
    @0
    cvol
    wf
    wph
    volf
    a1i
    wph
    @3
    cA
    wfn
    vx
    cv
    #
    @3
    cfv
    #
    @6
    wcel
    #
    vx
    cA
    wral
    @7
    @6
    wss
    wph
    cA
    cxr
    cpw
    #
    @3
    wph
    cxr
    cxr
    cxp
    #
    @11
    cr
    cxr
    cxp
    #
    cA
    cico
    cF
    @12
    @11
    cico
    wf
    wph
    icof
    a1i
    @13
    @12
    wss
    #
    wph
    cr
    cxr
    wss
    @14
    ressxr
    cr
    cxr
    cxr
    xpss1
    ax-mp
    a1i
    volicoff.1
    fcoss
    #
    ffnd
    wph
    @10
    vx
    cA
    wph
    @8
    cA
    wcel
    #
    wa
    #
    @9
    @8
    cF
    cfv
    #
    c1st
    cfv
    #
    @18
    c2nd
    cfv
    #
    cico
    co
    #
    @6
    @17
    cF
    cico
    cr
    cxr
    cA
    @8
    wph
    cA
    @13
    cF
    wf
    @16
    volicoff.1
    adantr
    wph
    @16
    simpr
    fvovco
    @17
    @19
    cr
    wcel
    #
    @20
    cxr
    wcel
    #
    @21
    @6
    wcel
    @17
    @18
    @13
    wcel
    #
    @22
    wph
    cA
    @13
    @8
    cF
    volicoff.1
    ffvelrnda
    #
    @18
    cr
    cxr
    xp1st
    syl
    @17
    @24
    @23
    @25
    @18
    cr
    cxr
    xp2nd
    syl
    @19
    @20
    icombl
    syl2anc
    eqeltrd
    ralrimiva
    vx
    cA
    @6
    @3
    fnfvrnss
    syl2anc
    wph
    cA
    @11
    @3
    wf
    cA
    @7
    @3
    wf
    @15
    cA
    @11
    @3
    ffrn
    syl
    fcoss
    @2
    @5
    wb
    wph
    cA
    @0
    @1
    @4
    cvol
    cico
    cF
    coass
    feq1i
    a1i
    mpbird
end

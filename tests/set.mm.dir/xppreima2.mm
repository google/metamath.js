include "ccnv.mm"
include "cxp.mm"
include "cima.mm"
include "c1st.mm"
include "ccom.mm"
include "c2nd.mm"
include "cin.mm"
include "wfun.mm"
include "crn.mm"
include "cvv.mm"
include "wss.mm"
include "wceq.mm"
include "cv.mm"
include "cfv.mm"
include "cop.mm"
include "funmpt2.mm"
include "wf.mm"
include "wcel.mm"
include "wa.mm"
include "ffvelrnda.mm"
include "opelxp.mm"
include "sylanbrc.mm"
include "fmptd.mm"
include "frn.mm"
include "syl.mm"
include "xpss.mm"
include "syl6ss.mm"
include "xppreima.mm"
include "sylancr.mm"
include "wfn.mm"
include "wfo.mm"
include "fo1st.mm"
include "fofn.mm"
include "ax-mp.mm"
include "opex.mm"
include "fnmpti.mm"
include "ssv.mm"
include "fnco.mm"
include "mp3an.mm"
include "a1i.mm"
include "ffn.mm"
include "cdm.mm"
include "adantr.mm"
include "simpr.mm"
include "dmmpti.mm"
include "syl6eleqr.mm"
include "opfv.mm"
include "syl21anc.mm"
include "fvmpt2.mm"
include "syl2anc.mm"
include "eqtr3d.mm"
include "fvex.mm"
include "opth.mm"
include "sylib.mm"
include "simpld.mm"
include "eqfnfvd.mm"
include "cnveqd.mm"
include "imaeq1d.mm"
include "fo2nd.mm"
include "simprd.mm"
include "ineq12d.mm"
include "eqtrd.mm"

theorem xppreima2
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F
  let cG: class G
  let cH: class H
  let cY: class Y
  let cZ: class Z
  assume xppreima2.1: |- ( ph -> F : A --> B )
  assume xppreima2.2: |- ( ph -> G : A --> C )
  assume xppreima2.3: |- H = ( x e. A |-> <. ( F ` x ) , ( G ` x ) >. )

  disjoint A x
  disjoint B x
  disjoint C x
  disjoint F x
  disjoint G x
  disjoint H x
  disjoint ph x
  assert |- ( ph -> ( `' H " ( Y X. Z ) ) = ( ( `' F " Y ) i^i ( `' G " Z ) ) )

  proof
    wph
    cH
    ccnv
    cY
    cZ
    cxp
    cima
    #
    c1st
    cH
    ccom
    #
    ccnv
    #
    cY
    cima
    #
    c2nd
    cH
    ccom
    #
    ccnv
    #
    cZ
    cima
    #
    cin
    #
    cF
    ccnv
    #
    cY
    cima
    #
    cG
    ccnv
    #
    cZ
    cima
    #
    cin
    wph
    cH
    wfun
    #
    cH
    crn
    #
    cvv
    cvv
    cxp
    #
    wss
    #
    @0
    @7
    wceq
    vx
    cA
    vx
    cv
    #
    cF
    cfv
    #
    @16
    cG
    cfv
    #
    cop
    #
    cH
    xppreima2.3
    funmpt2
    #
    wph
    @13
    cB
    cC
    cxp
    #
    @14
    wph
    cA
    @21
    cH
    wf
    @13
    @21
    wss
    wph
    vx
    cA
    @19
    @21
    cH
    wph
    @16
    cA
    wcel
    #
    wa
    #
    @17
    cB
    wcel
    @18
    cC
    wcel
    @19
    @21
    wcel
    #
    wph
    cA
    cB
    @16
    cF
    xppreima2.1
    ffvelrnda
    wph
    cA
    cC
    @16
    cG
    xppreima2.2
    ffvelrnda
    @17
    @18
    cB
    cC
    opelxp
    sylanbrc
    #
    xppreima2.3
    fmptd
    cA
    @21
    cH
    frn
    syl
    cB
    cC
    xpss
    syl6ss
    #
    cH
    cY
    cZ
    xppreima
    sylancr
    wph
    @3
    @9
    @6
    @11
    wph
    @2
    @8
    cY
    wph
    @1
    cF
    wph
    vx
    cA
    @1
    cF
    @1
    cA
    wfn
    #
    wph
    c1st
    cvv
    wfn
    #
    cH
    cA
    wfn
    #
    @13
    cvv
    wss
    #
    @27
    cvv
    cvv
    c1st
    wfo
    @28
    fo1st
    cvv
    cvv
    c1st
    fofn
    ax-mp
    vx
    cA
    @19
    cH
    @17
    @18
    opex
    #
    xppreima2.3
    fnmpti
    #
    @13
    ssv
    #
    cvv
    cA
    c1st
    cH
    fnco
    mp3an
    a1i
    wph
    cA
    cB
    cF
    wf
    cF
    cA
    wfn
    xppreima2.1
    cA
    cB
    cF
    ffn
    syl
    @23
    @16
    @1
    cfv
    #
    @17
    wceq
    #
    @16
    @4
    cfv
    #
    @18
    wceq
    #
    @23
    @34
    @36
    cop
    #
    @19
    wceq
    @35
    @37
    wa
    @23
    @16
    cH
    cfv
    #
    @38
    @19
    @23
    @12
    @15
    @16
    cH
    cdm
    #
    wcel
    @39
    @38
    wceq
    @12
    @23
    @20
    a1i
    wph
    @15
    @22
    @26
    adantr
    @23
    @16
    cA
    @40
    wph
    @22
    simpr
    #
    vx
    cA
    @19
    cH
    @31
    xppreima2.3
    dmmpti
    syl6eleqr
    vx
    cH
    opfv
    syl21anc
    @23
    @22
    @24
    @39
    @19
    wceq
    @41
    @25
    vx
    cA
    @19
    @21
    cH
    xppreima2.3
    fvmpt2
    syl2anc
    eqtr3d
    @34
    @36
    @17
    @18
    @16
    @1
    fvex
    @16
    @4
    fvex
    opth
    sylib
    #
    simpld
    eqfnfvd
    cnveqd
    imaeq1d
    wph
    @5
    @10
    cZ
    wph
    @4
    cG
    wph
    vx
    cA
    @4
    cG
    @4
    cA
    wfn
    #
    wph
    c2nd
    cvv
    wfn
    #
    @29
    @30
    @43
    cvv
    cvv
    c2nd
    wfo
    @44
    fo2nd
    cvv
    cvv
    c2nd
    fofn
    ax-mp
    @32
    @33
    cvv
    cA
    c2nd
    cH
    fnco
    mp3an
    a1i
    wph
    cA
    cC
    cG
    wf
    cG
    cA
    wfn
    xppreima2.2
    cA
    cC
    cG
    ffn
    syl
    @23
    @35
    @37
    @42
    simprd
    eqfnfvd
    cnveqd
    imaeq1d
    ineq12d
    eqtrd
end

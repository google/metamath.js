include "cc0.mm"
include "wceq.mm"
include "ccn.mm"
include "co.mm"
include "wcel.mm"
include "cpnf.mm"
include "cioo.mm"
include "cicc.mm"
include "ctopon.mm"
include "cfv.mm"
include "csn.mm"
include "wf.mm"
include "cle.mm"
include "cordt.mm"
include "crest.mm"
include "cxr.mm"
include "wss.mm"
include "letopon.mm"
include "iccssxr.mm"
include "resttopon.mm"
include "mp2an.mm"
include "eqeltri.mm"
include "a1i.mm"
include "0e0iccpnf.mm"
include "cxp.mm"
include "cv.mm"
include "cxmu.mm"
include "cmpt.mm"
include "wa.mm"
include "simpl.mm"
include "oveq2d.mm"
include "simpr.mm"
include "sseldi.mm"
include "xmul01.mm"
include "syl.mm"
include "eqtrd.mm"
include "mpteq2dva.mm"
include "fconstmpt.mm"
include "3eqtr4g.mm"
include "c0ex.mm"
include "fconst2.mm"
include "sylibr.mm"
include "cnconst.mm"
include "syl22anc.mm"
include "adantl.mm"
include "crp.mm"
include "cres.mm"
include "eqid.mm"
include "oveq1.mm"
include "cbvmptv.mm"
include "id.mm"
include "xrmulc1cn.mm"
include "letopuni.mm"
include "cnrest.mm"
include "sylancl.mm"
include "resmpt.mm"
include "ax-mp.mm"
include "eqtr4i.mm"
include "eqcomi.mm"
include "oveq1i.mm"
include "3eltr3g.mm"
include "crn.mm"
include "wb.mm"
include "ioorp.mm"
include "ioossicc.mm"
include "eqsstr3i.mm"
include "ge0xmulcl.mm"
include "syl2anc.mm"
include "fmptd.mm"
include "frn.mm"
include "cnrest2.mm"
include "syl3anc.mm"
include "mpbid.mm"
include "oveq2i.mm"
include "syl6eleqr.mm"
include "eleq2s.mm"
include "cico.mm"
include "wo.mm"
include "clt.mm"
include "wbr.mm"
include "0xr.mm"
include "pnfxr.mm"
include "0ltpnf.mm"
include "elicoelioo.mm"
include "mp3an.mm"
include "sylib.mm"
include "mpjaodan.mm"

theorem xrge0mulc1cn
  let wph: wff ph
  let vx: setvar x
  let cC: class C
  let cF: class F
  let cJ: class J
  let vy: setvar y
  assume xrge0mulc1cn.k: |- J = ( ( ordTop ` <_ ) |`t ( 0 [,] +oo ) )
  assume xrge0mulc1cn.f: |- F = ( x e. ( 0 [,] +oo ) |-> ( x *e C ) )
  assume xrge0mulc1cn.c: |- ( ph -> C e. ( 0 [,) +oo ) )

  disjoint C x
  disjoint x y
  disjoint C y
  assert |- ( ph -> F e. ( J Cn J ) )

  proof
    wph
    cC
    cc0
    wceq
    #
    cF
    cJ
    cJ
    ccn
    co
    #
    wcel
    #
    cC
    cc0
    cpnf
    cioo
    co
    #
    wcel
    #
    @0
    @2
    wph
    @0
    cJ
    cc0
    cpnf
    cicc
    co
    #
    ctopon
    cfv
    #
    wcel
    #
    @7
    cc0
    @5
    wcel
    #
    @5
    cc0
    csn
    #
    cF
    wf
    #
    @2
    @7
    @0
    cJ
    cle
    cordt
    cfv
    #
    @5
    crest
    co
    #
    @6
    xrge0mulc1cn.k
    @11
    cxr
    ctopon
    cfv
    wcel
    #
    @5
    cxr
    wss
    #
    @12
    @6
    wcel
    letopon
    cc0
    cpnf
    iccssxr
    #
    @5
    @11
    cxr
    resttopon
    mp2an
    eqeltri
    a1i
    #
    @16
    @8
    @0
    0e0iccpnf
    a1i
    @0
    cF
    @5
    @9
    cxp
    #
    wceq
    @10
    @0
    vx
    @5
    vx
    cv
    #
    cC
    cxmu
    co
    #
    cmpt
    #
    vx
    @5
    cc0
    cmpt
    cF
    @17
    @0
    vx
    @5
    @19
    cc0
    @0
    @18
    @5
    wcel
    #
    wa
    #
    @19
    @18
    cc0
    cxmu
    co
    #
    cc0
    @22
    cC
    cc0
    @18
    cxmu
    @0
    @21
    simpl
    oveq2d
    @22
    @18
    cxr
    wcel
    @23
    cc0
    wceq
    @22
    @5
    cxr
    @18
    @15
    @0
    @21
    simpr
    sseldi
    @18
    xmul01
    syl
    eqtrd
    mpteq2dva
    xrge0mulc1cn.f
    vx
    @5
    cc0
    fconstmpt
    3eqtr4g
    @5
    cc0
    cF
    c0ex
    fconst2
    sylibr
    cc0
    cF
    cJ
    cJ
    @5
    @5
    cnconst
    syl22anc
    adantl
    @4
    @2
    wph
    @2
    cC
    crp
    @3
    cC
    crp
    wcel
    #
    cF
    cJ
    @12
    ccn
    co
    #
    @1
    @24
    cF
    cJ
    @11
    ccn
    co
    #
    wcel
    #
    cF
    @25
    wcel
    #
    @24
    vx
    cxr
    @19
    cmpt
    #
    @5
    cres
    #
    @12
    @11
    ccn
    co
    #
    cF
    @26
    @24
    @29
    @11
    @11
    ccn
    co
    wcel
    @14
    @30
    @31
    wcel
    @24
    vy
    cC
    @29
    @11
    @11
    eqid
    vx
    vy
    cxr
    @19
    vy
    cv
    #
    cC
    cxmu
    co
    @18
    @32
    cC
    cxmu
    oveq1
    cbvmptv
    @24
    id
    xrmulc1cn
    @15
    @5
    @29
    @11
    @11
    cxr
    letopuni
    cnrest
    sylancl
    @30
    @20
    cF
    @14
    @30
    @20
    wceq
    @15
    vx
    cxr
    @5
    @19
    resmpt
    ax-mp
    xrge0mulc1cn.f
    eqtr4i
    @12
    cJ
    @11
    ccn
    cJ
    @12
    xrge0mulc1cn.k
    eqcomi
    oveq1i
    3eltr3g
    @24
    @13
    cF
    crn
    @5
    wss
    #
    @14
    @27
    @28
    wb
    @13
    @24
    letopon
    a1i
    @24
    @5
    @5
    cF
    wf
    @33
    @24
    vx
    @5
    @19
    @5
    cF
    @24
    @21
    wa
    #
    @21
    cC
    @5
    wcel
    @19
    @5
    wcel
    @24
    @21
    simpr
    @34
    crp
    @5
    cC
    crp
    @3
    @5
    ioorp
    cc0
    cpnf
    ioossicc
    eqsstr3i
    @24
    @21
    simpl
    sseldi
    @18
    cC
    ge0xmulcl
    syl2anc
    xrge0mulc1cn.f
    fmptd
    @5
    @5
    cF
    frn
    syl
    @14
    @24
    @15
    a1i
    @5
    cF
    cJ
    @11
    cxr
    cnrest2
    syl3anc
    mpbid
    cJ
    @12
    cJ
    ccn
    xrge0mulc1cn.k
    oveq2i
    syl6eleqr
    ioorp
    eleq2s
    adantl
    wph
    cC
    cc0
    cpnf
    cico
    co
    wcel
    #
    @0
    @4
    wo
    #
    xrge0mulc1cn.c
    cc0
    cxr
    wcel
    cpnf
    cxr
    wcel
    cc0
    cpnf
    clt
    wbr
    @35
    @36
    wb
    0xr
    pnfxr
    0ltpnf
    cc0
    cpnf
    cC
    elicoelioo
    mp3an
    sylib
    mpjaodan
end

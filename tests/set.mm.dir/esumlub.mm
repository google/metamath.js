include "cxrs.mm"
include "cc0.mm"
include "cpnf.mm"
include "cicc.mm"
include "co.mm"
include "cress.mm"
include "cv.mm"
include "cmpt.mm"
include "cgsu.mm"
include "clt.mm"
include "wbr.mm"
include "cpw.mm"
include "cfn.mm"
include "cin.mm"
include "wrex.mm"
include "cesum.mm"
include "crn.mm"
include "cxr.mm"
include "csup.mm"
include "nfcv.mm"
include "wcel.mm"
include "wa.mm"
include "eqidd.mm"
include "esumval.mm"
include "breq2d.mm"
include "wss.mm"
include "wb.mm"
include "wral.mm"
include "iccssxr.mm"
include "xrge0base.mm"
include "ccmn.mm"
include "xrge0cmn.mm"
include "a1i.mm"
include "inss2.mm"
include "simpr.mm"
include "sseldi.mm"
include "nfv.mm"
include "nfan.mm"
include "simpll.mm"
include "inss1.mm"
include "sseli.mm"
include "ad2antlr.mm"
include "elpwid.mm"
include "sseldd.mm"
include "syl2anc.mm"
include "ex.mm"
include "ralrimi.mm"
include "gsummptcl.mm"
include "ralrimiva.mm"
include "eqid.mm"
include "rnmptss.mm"
include "syl.mm"
include "supxrlub.mm"
include "bitrd.mm"
include "mpbid.mm"
include "cvv.mm"
include "ovex.mm"
include "wceq.mm"
include "mpteq1.mm"
include "oveq2d.mm"
include "cbvmptv.mm"
include "elrnmpti.mm"
include "rexxfr2d.mm"
include "gsumesum.mm"
include "biimpd.mm"
include "reximdva.mm"
include "mpd.mm"

theorem esumlub
  let wph: wff ph
  let cA: class A
  let cB: class B
  let vk: setvar k
  let cV: class V
  let cX: class X
  let va: setvar a
  let vx: setvar x
  let vy: setvar y
  assume esumlub.f: |- F/ k ph
  assume esumlub.0: |- ( ph -> A e. V )
  assume esumlub.1: |- ( ( ph /\ k e. A ) -> B e. ( 0 [,] +oo ) )
  assume esumlub.2: |- ( ph -> X e. RR* )
  assume esumlub.3: |- ( ph -> X < sum* k e. A B )

  disjoint a k
  disjoint A a
  disjoint A k
  disjoint B a
  disjoint X a
  disjoint a ph
  disjoint a x
  disjoint a y
  disjoint k x
  disjoint k y
  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B x
  disjoint B y
  disjoint X y
  disjoint ph x
  disjoint ph y
  assert |- ( ph -> E. a e. ( ~P A i^i Fin ) X < sum* k e. a B )

  proof
    wph
    cX
    cxrs
    cc0
    cpnf
    cicc
    co
    #
    cress
    co
    #
    vk
    va
    cv
    #
    cB
    cmpt
    #
    cgsu
    co
    #
    clt
    wbr
    #
    va
    cA
    cpw
    #
    cfn
    cin
    #
    wrex
    #
    cX
    @2
    cB
    vk
    cesum
    #
    clt
    wbr
    #
    va
    @7
    wrex
    wph
    cX
    vy
    cv
    #
    clt
    wbr
    #
    vy
    vx
    @7
    @1
    vk
    vx
    cv
    #
    cB
    cmpt
    #
    cgsu
    co
    #
    cmpt
    #
    crn
    #
    wrex
    #
    @8
    wph
    cX
    cA
    cB
    vk
    cesum
    #
    clt
    wbr
    #
    @18
    esumlub.3
    wph
    @20
    cX
    @17
    cxr
    clt
    csup
    #
    clt
    wbr
    #
    @18
    wph
    @19
    @21
    cX
    clt
    wph
    vx
    cA
    cB
    @15
    vk
    cV
    esumlub.f
    vk
    cA
    nfcv
    esumlub.0
    esumlub.1
    wph
    @13
    @7
    wcel
    #
    wa
    #
    @15
    eqidd
    esumval
    breq2d
    wph
    @17
    cxr
    wss
    #
    cX
    cxr
    wcel
    @22
    @18
    wb
    wph
    @15
    cxr
    wcel
    #
    vx
    @7
    wral
    @25
    wph
    @26
    vx
    @7
    @24
    @0
    cxr
    @15
    cc0
    cpnf
    iccssxr
    @24
    @0
    vk
    @1
    @13
    cB
    xrge0base
    @1
    ccmn
    wcel
    @24
    xrge0cmn
    a1i
    @24
    @7
    cfn
    @13
    @6
    cfn
    inss2
    #
    wph
    @23
    simpr
    sseldi
    @24
    cB
    @0
    wcel
    #
    vk
    @13
    wph
    @23
    vk
    esumlub.f
    @23
    vk
    nfv
    nfan
    @24
    vk
    cv
    #
    @13
    wcel
    #
    @28
    @24
    @30
    wa
    #
    wph
    @29
    cA
    wcel
    #
    @28
    wph
    @23
    @30
    simpll
    @31
    @13
    cA
    @29
    @31
    @13
    cA
    @23
    @13
    @6
    wcel
    wph
    @30
    @7
    @6
    @13
    @6
    cfn
    inss1
    #
    sseli
    ad2antlr
    elpwid
    @24
    @30
    simpr
    sseldd
    esumlub.1
    syl2anc
    ex
    ralrimi
    gsummptcl
    sseldi
    ralrimiva
    vx
    @7
    @15
    cxr
    @16
    @16
    eqid
    rnmptss
    syl
    esumlub.2
    vy
    @17
    cX
    supxrlub
    syl2anc
    bitrd
    mpbid
    wph
    @12
    @5
    vy
    va
    @4
    @17
    @7
    cvv
    @4
    cvv
    wcel
    wph
    @2
    @7
    wcel
    #
    wa
    #
    @1
    @3
    cgsu
    ovex
    #
    a1i
    @11
    @17
    wcel
    @11
    @4
    wceq
    #
    va
    @7
    wrex
    wb
    wph
    va
    @7
    @4
    @11
    @16
    vx
    va
    @7
    @15
    @4
    @13
    @2
    wceq
    @14
    @3
    @1
    cgsu
    vk
    @13
    @2
    cB
    mpteq1
    oveq2d
    cbvmptv
    @36
    elrnmpti
    a1i
    wph
    @37
    wa
    @11
    @4
    cX
    clt
    wph
    @37
    simpr
    breq2d
    rexxfr2d
    mpbid
    wph
    @5
    @10
    va
    @7
    @35
    @5
    @10
    @35
    @4
    @9
    cX
    clt
    @35
    @2
    cB
    vk
    wph
    @34
    vk
    esumlub.f
    @34
    vk
    nfv
    nfan
    @35
    @7
    cfn
    @2
    @27
    wph
    @34
    simpr
    sseldi
    @35
    @29
    @2
    wcel
    #
    wa
    #
    wph
    @32
    @28
    wph
    @34
    @38
    simpll
    @39
    @2
    cA
    @29
    @39
    @2
    cA
    @34
    @2
    @6
    wcel
    wph
    @38
    @7
    @6
    @2
    @33
    sseli
    ad2antlr
    elpwid
    @35
    @38
    simpr
    sseldd
    esumlub.1
    syl2anc
    gsumesum
    breq2d
    biimpd
    reximdva
    mpd
end

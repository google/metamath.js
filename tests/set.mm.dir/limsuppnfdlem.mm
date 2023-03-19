include "clsp.mm"
include "cfv.mm"
include "crn.mm"
include "cxr.mm"
include "clt.mm"
include "cinf.mm"
include "cpnf.mm"
include "csn.mm"
include "cvv.mm"
include "wcel.mm"
include "wceq.mm"
include "cr.mm"
include "reex.mm"
include "a1i.mm"
include "ssexd.mm"
include "fexd.mm"
include "limsupval.mm"
include "syl.mm"
include "cmpt.mm"
include "cv.mm"
include "cico.mm"
include "co.mm"
include "cima.mm"
include "cin.mm"
include "csup.mm"
include "wa.mm"
include "cle.mm"
include "wbr.mm"
include "wrex.mm"
include "wral.mm"
include "r19.21bi.mm"
include "an32s.mm"
include "wfun.mm"
include "cdm.mm"
include "ffund.mm"
include "adantr.mm"
include "simpr.mm"
include "fdmd.mm"
include "eleqtrrd.mm"
include "jca.mm"
include "ad4ant13.mm"
include "simpllr.mm"
include "rexrd.mm"
include "pnfxr.mm"
include "wss.mm"
include "ressxr.mm"
include "sstrd.mm"
include "sseldd.mm"
include "sselda.mm"
include "ltpnf.mm"
include "elicod.mm"
include "funfvima.mm"
include "sylc.mm"
include "ffvelrnda.mm"
include "elind.mm"
include "adantllr.mm"
include "adantrr.mm"
include "simprr.mm"
include "nfv.mm"
include "breq2.mm"
include "rspce.mm"
include "syl2anc.mm"
include "ex.mm"
include "rexlimdva.mm"
include "mpd.mm"
include "ralrimiva.mm"
include "wb.mm"
include "inss2.mm"
include "supxrunb3.mm"
include "mpbid.mm"
include "mpteq2dva.mm"
include "eqtrd.mm"
include "rneqd.mm"
include "eqid.mm"
include "c0.mm"
include "wne.mm"
include "ren0.mm"
include "rnmptc.mm"
include "infeq1d.mm"
include "wor.mm"
include "xrltso.mm"
include "pm3.2i.mm"
include "infsn.mm"
include "ax-mp.mm"
include "3eqtrd.mm"

theorem limsuppnfdlem
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let vj: setvar j
  let vk: setvar k
  let cF: class F
  let cG: class G
  let vy: setvar y
  assume limsuppnfdlem.a: |- ( ph -> A C_ RR )
  assume limsuppnfdlem.f: |- ( ph -> F : A --> RR* )
  assume limsuppnfdlem.u: |- ( ph -> A. x e. RR A. k e. RR E. j e. A ( k <_ j /\ x <_ ( F ` j ) ) )
  assume limsuppnfdlem.g: |- G = ( k e. RR |-> sup ( ( ( F " ( k [,) +oo ) ) i^i RR* ) , RR* , < ) )

  disjoint F j
  disjoint F k
  disjoint F x
  disjoint j k
  disjoint j x
  disjoint k x
  disjoint j ph
  disjoint k ph
  disjoint ph x
  disjoint F y
  disjoint j y
  disjoint k y
  disjoint x y
  assert |- ( ph -> ( limsup ` F ) = +oo )

  proof
    wph
    cF
    clsp
    cfv
    #
    cG
    crn
    #
    cxr
    clt
    cinf
    #
    cpnf
    csn
    #
    cxr
    clt
    cinf
    #
    cpnf
    wph
    cF
    cvv
    wcel
    @0
    @2
    wceq
    wph
    cA
    cxr
    cvv
    cF
    limsuppnfdlem.f
    wph
    cA
    cr
    cvv
    cr
    cvv
    wcel
    wph
    reex
    a1i
    limsuppnfdlem.a
    ssexd
    fexd
    vk
    cF
    cG
    cvv
    limsuppnfdlem.g
    limsupval
    syl
    wph
    cxr
    @1
    @3
    clt
    wph
    @1
    vk
    cr
    cpnf
    cmpt
    #
    crn
    @3
    wph
    cG
    @5
    wph
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
    csup
    #
    cmpt
    #
    @5
    cG
    @11
    wceq
    wph
    limsuppnfdlem.g
    a1i
    wph
    vk
    cr
    @10
    cpnf
    wph
    @6
    cr
    wcel
    #
    wa
    #
    vx
    cv
    #
    vy
    cv
    #
    cle
    wbr
    #
    vy
    @9
    wrex
    #
    vx
    cr
    wral
    #
    @10
    cpnf
    wceq
    #
    @13
    @17
    vx
    cr
    @13
    @14
    cr
    wcel
    #
    wa
    #
    @6
    vj
    cv
    #
    cle
    wbr
    #
    @14
    @22
    cF
    cfv
    #
    cle
    wbr
    #
    wa
    #
    vj
    cA
    wrex
    #
    @17
    wph
    @20
    @12
    @27
    wph
    @20
    wa
    @27
    vk
    cr
    wph
    @27
    vk
    cr
    wral
    vx
    cr
    limsuppnfdlem.u
    r19.21bi
    r19.21bi
    an32s
    @21
    @26
    @17
    vj
    cA
    @21
    @22
    cA
    wcel
    #
    wa
    #
    @26
    @17
    @29
    @26
    wa
    @24
    @9
    wcel
    #
    @25
    @17
    @29
    @23
    @30
    @25
    @13
    @28
    @23
    @30
    @20
    @13
    @28
    wa
    #
    @23
    wa
    #
    @8
    cxr
    @24
    @32
    cF
    wfun
    #
    @22
    cF
    cdm
    #
    wcel
    #
    wa
    #
    @22
    @7
    wcel
    @24
    @8
    wcel
    wph
    @28
    @36
    @12
    @23
    wph
    @28
    wa
    #
    @33
    @35
    wph
    @33
    @28
    wph
    cA
    cxr
    cF
    limsuppnfdlem.f
    ffund
    adantr
    @37
    @22
    cA
    @34
    wph
    @28
    simpr
    #
    wph
    @34
    cA
    wceq
    @28
    wph
    cA
    cxr
    cF
    limsuppnfdlem.f
    fdmd
    adantr
    eleqtrrd
    jca
    ad4ant13
    @32
    @6
    cpnf
    @22
    @32
    @6
    wph
    @12
    @28
    @23
    simpllr
    rexrd
    cpnf
    cxr
    wcel
    #
    @32
    pnfxr
    a1i
    wph
    @28
    @22
    cxr
    wcel
    @12
    @23
    @37
    cA
    cxr
    @22
    wph
    cA
    cxr
    wss
    @28
    wph
    cA
    cr
    cxr
    limsuppnfdlem.a
    cr
    cxr
    wss
    wph
    ressxr
    a1i
    sstrd
    adantr
    @38
    sseldd
    ad4ant13
    @31
    @23
    simpr
    wph
    @28
    @22
    cpnf
    clt
    wbr
    #
    @12
    @23
    @37
    @22
    cr
    wcel
    @40
    wph
    cA
    cr
    @22
    limsuppnfdlem.a
    sselda
    @22
    ltpnf
    syl
    ad4ant13
    elicod
    @7
    @22
    cF
    funfvima
    sylc
    wph
    @28
    @24
    cxr
    wcel
    @12
    @23
    wph
    cA
    cxr
    @22
    cF
    limsuppnfdlem.f
    ffvelrnda
    ad4ant13
    elind
    adantllr
    adantrr
    @29
    @23
    @25
    simprr
    @16
    @25
    vy
    @24
    @9
    @25
    vy
    nfv
    @15
    @24
    @14
    cle
    breq2
    rspce
    syl2anc
    ex
    rexlimdva
    mpd
    ralrimiva
    @13
    @9
    cxr
    wss
    #
    @18
    @19
    wb
    @41
    @13
    @8
    cxr
    inss2
    a1i
    vx
    vy
    @9
    supxrunb3
    syl
    mpbid
    mpteq2dva
    eqtrd
    rneqd
    wph
    vk
    cr
    cpnf
    cxr
    @5
    @5
    eqid
    @39
    @13
    pnfxr
    a1i
    cr
    c0
    wne
    wph
    ren0
    a1i
    rnmptc
    eqtrd
    infeq1d
    @4
    cpnf
    wceq
    #
    wph
    cxr
    clt
    wor
    #
    @39
    wa
    @42
    @43
    @39
    xrltso
    pnfxr
    pm3.2i
    cxr
    cpnf
    clt
    infsn
    ax-mp
    a1i
    3eqtrd
end

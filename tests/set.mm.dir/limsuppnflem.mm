include "clsp.mm"
include "cfv.mm"
include "cpnf.mm"
include "wceq.mm"
include "cv.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "wrex.mm"
include "cr.mm"
include "wral.mm"
include "clt.mm"
include "wn.mm"
include "wi.mm"
include "id.mm"
include "imnan.mm"
include "ralbii.mm"
include "ralnex.mm"
include "bitri.mm"
include "rexbii.mm"
include "rexnal.mm"
include "biimpri.mm"
include "wcel.mm"
include "w3a.mm"
include "simp1.mm"
include "imp.mm"
include "3adant1.mm"
include "cxr.mm"
include "ffvelrnda.mm"
include "ad4ant14.mm"
include "adantr.mm"
include "simpllr.mm"
include "rexr.mm"
include "syl.mm"
include "simpr.mm"
include "ad4ant13.mm"
include "ad3antlr.mm"
include "xrltnled.mm"
include "mpbird.mm"
include "adantllr.mm"
include "xrltled.mm"
include "syl2anc.mm"
include "3exp.mm"
include "ralimdva.mm"
include "reximdva.mm"
include "syl2an.mm"
include "cvv.mm"
include "reex.mm"
include "a1i.mm"
include "ssexd.mm"
include "fexd.mm"
include "limsupcld.mm"
include "ad2antrr.mm"
include "ad2antlr.mm"
include "pnfxr.mm"
include "wss.mm"
include "wf.mm"
include "limsupbnd1f.mm"
include "ltpnf.mm"
include "xrlelttrd.mm"
include "ex.mm"
include "rexlimdva.mm"
include "syldan.mm"
include "adantlr.mm"
include "eqeltrd.mm"
include "xreqnltd.mm"
include "adantl.mm"
include "condan.mm"
include "limsuppnfd.mm"
include "impbid.mm"

theorem limsuppnflem
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let vj: setvar j
  let vk: setvar k
  let cF: class F
  assume limsuppnflem.j: |- F/_ j F
  assume limsuppnflem.a: |- ( ph -> A C_ RR )
  assume limsuppnflem.f: |- ( ph -> F : A --> RR* )

  disjoint A j
  disjoint A k
  disjoint A x
  disjoint j k
  disjoint j x
  disjoint k x
  disjoint F k
  disjoint F x
  disjoint j ph
  disjoint k ph
  disjoint ph x
  assert |- ( ph -> ( ( limsup ` F ) = +oo <-> A. x e. RR A. k e. RR E. j e. A ( k <_ j /\ x <_ ( F ` j ) ) ) )

  proof
    wph
    cF
    clsp
    cfv
    #
    cpnf
    wceq
    #
    vk
    cv
    #
    vj
    cv
    #
    cle
    wbr
    #
    vx
    cv
    #
    @3
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
    vk
    cr
    wral
    #
    vx
    cr
    wral
    #
    wph
    @1
    @11
    wph
    @1
    wa
    #
    @11
    @0
    cpnf
    clt
    wbr
    #
    wph
    @11
    wn
    #
    @13
    @1
    wph
    @14
    @4
    @6
    @5
    cle
    wbr
    #
    wi
    #
    vj
    cA
    wral
    #
    vk
    cr
    wrex
    #
    vx
    cr
    wrex
    #
    @13
    wph
    wph
    @4
    @7
    wn
    #
    wi
    #
    vj
    cA
    wral
    #
    vk
    cr
    wrex
    #
    vx
    cr
    wrex
    #
    @19
    @14
    wph
    id
    @24
    @14
    @24
    @10
    wn
    #
    vx
    cr
    wrex
    @14
    @23
    @25
    vx
    cr
    @23
    @9
    wn
    #
    vk
    cr
    wrex
    @25
    @22
    @26
    vk
    cr
    @22
    @8
    wn
    #
    vj
    cA
    wral
    @26
    @21
    @27
    vj
    cA
    @4
    @7
    imnan
    ralbii
    @8
    vj
    cA
    ralnex
    bitri
    rexbii
    @9
    vk
    cr
    rexnal
    bitri
    rexbii
    @10
    vx
    cr
    rexnal
    bitri
    biimpri
    wph
    @24
    @19
    wph
    @23
    @18
    vx
    cr
    wph
    @5
    cr
    wcel
    #
    wa
    #
    @22
    @17
    vk
    cr
    @29
    @2
    cr
    wcel
    #
    wa
    #
    @21
    @16
    vj
    cA
    @31
    @3
    cA
    wcel
    #
    wa
    #
    @21
    @4
    @15
    @33
    @21
    @4
    w3a
    @33
    @20
    @15
    @33
    @21
    @4
    simp1
    @21
    @4
    @20
    @33
    @21
    @4
    @20
    @21
    id
    imp
    3adant1
    @33
    @20
    wa
    @6
    @5
    @33
    @6
    cxr
    wcel
    #
    @20
    wph
    @32
    @34
    @28
    @30
    wph
    cA
    cxr
    @3
    cF
    limsuppnflem.f
    ffvelrnda
    #
    ad4ant14
    adantr
    @33
    @5
    cxr
    wcel
    #
    @20
    @33
    @28
    @36
    wph
    @28
    @30
    @32
    simpllr
    @5
    rexr
    #
    syl
    adantr
    @29
    @32
    @20
    @6
    @5
    clt
    wbr
    #
    @30
    @29
    @32
    wa
    #
    @20
    wa
    #
    @38
    @20
    @39
    @20
    simpr
    @40
    @6
    @5
    wph
    @32
    @34
    @28
    @20
    @35
    ad4ant13
    @28
    @36
    wph
    @32
    @20
    @37
    ad3antlr
    xrltnled
    mpbird
    adantllr
    xrltled
    syl2anc
    3exp
    ralimdva
    reximdva
    reximdva
    imp
    syl2an
    wph
    @19
    @13
    wph
    @18
    @13
    vx
    cr
    @29
    @18
    @13
    @29
    @18
    wa
    #
    @0
    @5
    cpnf
    wph
    @0
    cxr
    wcel
    @28
    @18
    wph
    cF
    cvv
    wph
    cA
    cxr
    cvv
    cF
    limsuppnflem.f
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
    limsuppnflem.a
    ssexd
    fexd
    limsupcld
    ad2antrr
    @28
    @36
    wph
    @18
    @37
    ad2antlr
    #
    cpnf
    cxr
    wcel
    #
    @41
    pnfxr
    a1i
    @41
    @5
    cA
    vj
    vk
    cF
    limsuppnflem.j
    wph
    cA
    cr
    wss
    #
    @28
    @18
    limsuppnflem.a
    ad2antrr
    wph
    cA
    cxr
    cF
    wf
    #
    @28
    @18
    limsuppnflem.f
    ad2antrr
    @42
    @29
    @18
    simpr
    limsupbnd1f
    @28
    @5
    cpnf
    clt
    wbr
    wph
    @18
    @5
    ltpnf
    ad2antlr
    xrlelttrd
    ex
    rexlimdva
    imp
    syldan
    adantlr
    @12
    @13
    wn
    #
    @14
    @1
    @46
    wph
    @1
    @0
    cpnf
    @1
    @0
    cpnf
    cxr
    @1
    id
    #
    @43
    @1
    pnfxr
    a1i
    eqeltrd
    @47
    xreqnltd
    adantl
    adantr
    condan
    ex
    wph
    @11
    @1
    wph
    @11
    wa
    vx
    cA
    vj
    vk
    cF
    limsuppnflem.j
    wph
    @44
    @11
    limsuppnflem.a
    adantr
    wph
    @45
    @11
    limsuppnflem.f
    adantr
    wph
    @11
    simpr
    limsuppnfd
    ex
    impbid
end

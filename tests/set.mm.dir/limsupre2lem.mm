include "clsp.mm"
include "cfv.mm"
include "cr.mm"
include "wcel.mm"
include "cmnf.mm"
include "wne.mm"
include "cpnf.mm"
include "wa.mm"
include "cv.mm"
include "cle.mm"
include "wbr.mm"
include "clt.mm"
include "wrex.mm"
include "wral.mm"
include "wi.mm"
include "cxr.mm"
include "wb.mm"
include "cvv.mm"
include "reex.mm"
include "a1i.mm"
include "ssexd.mm"
include "fexd.mm"
include "limsupcld.mm"
include "xrre4.mm"
include "syl.mm"
include "wceq.mm"
include "wn.mm"
include "df-ne.mm"
include "limsupmnf.mm"
include "notbid.mm"
include "annim.mm"
include "rexbii.mm"
include "rexnal.mm"
include "bitri.mm"
include "ralbii.mm"
include "ralnex.mm"
include "bitr2i.mm"
include "simplr.mm"
include "rexrd.mm"
include "wf.mm"
include "adantr.mm"
include "ffvelrnda.mm"
include "xrltnled.mm"
include "bicomd.mm"
include "anbi2d.mm"
include "rexbidva.mm"
include "ralbidv.mm"
include "bitrd.mm"
include "3bitrd.mm"
include "limsuppnf.mm"
include "imbi2d.mm"
include "ralbidva.mm"
include "rexbidv.mm"
include "imnan.mm"
include "bitr2d.mm"
include "anbi12d.mm"

theorem limsupre2lem
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let vj: setvar j
  let vk: setvar k
  let cF: class F
  assume limsupre2lem.1: |- F/_ j F
  assume limsupre2lem.2: |- ( ph -> A C_ RR )
  assume limsupre2lem.3: |- ( ph -> F : A --> RR* )

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
  assert |- ( ph -> ( ( limsup ` F ) e. RR <-> ( E. x e. RR A. k e. RR E. j e. A ( k <_ j /\ x < ( F ` j ) ) /\ E. x e. RR E. k e. RR A. j e. A ( k <_ j -> ( F ` j ) < x ) ) ) )

  proof
    wph
    cF
    clsp
    cfv
    #
    cr
    wcel
    #
    @0
    cmnf
    wne
    #
    @0
    cpnf
    wne
    #
    wa
    #
    vk
    cv
    vj
    cv
    #
    cle
    wbr
    #
    vx
    cv
    #
    @5
    cF
    cfv
    #
    clt
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
    wrex
    #
    @6
    @8
    @7
    clt
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
    wa
    wph
    @0
    cxr
    wcel
    @1
    @4
    wb
    wph
    cF
    cvv
    wph
    cA
    cxr
    cvv
    cF
    limsupre2lem.3
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
    limsupre2lem.2
    ssexd
    fexd
    limsupcld
    @0
    xrre4
    syl
    wph
    @2
    @13
    @3
    @18
    wph
    @2
    @0
    cmnf
    wceq
    #
    wn
    #
    @6
    @8
    @7
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
    wral
    #
    wn
    #
    @13
    @2
    @20
    wb
    wph
    @0
    cmnf
    df-ne
    a1i
    wph
    @19
    @25
    wph
    vx
    cA
    vj
    vk
    cF
    limsupre2lem.1
    limsupre2lem.2
    limsupre2lem.3
    limsupmnf
    notbid
    wph
    @26
    @6
    @21
    wn
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
    wrex
    #
    @13
    @26
    @31
    wb
    wph
    @31
    @24
    wn
    #
    vx
    cr
    wrex
    @26
    @30
    @32
    vx
    cr
    @30
    @23
    wn
    #
    vk
    cr
    wral
    @32
    @29
    @33
    vk
    cr
    @29
    @22
    wn
    #
    vj
    cA
    wrex
    @33
    @28
    @34
    vj
    cA
    @6
    @21
    annim
    rexbii
    @22
    vj
    cA
    rexnal
    bitri
    ralbii
    @23
    vk
    cr
    ralnex
    bitri
    rexbii
    @24
    vx
    cr
    rexnal
    bitr2i
    a1i
    wph
    @30
    @12
    vx
    cr
    wph
    @7
    cr
    wcel
    #
    wa
    #
    @29
    @11
    vk
    cr
    @36
    @28
    @10
    vj
    cA
    @36
    @5
    cA
    wcel
    #
    wa
    #
    @27
    @9
    @6
    @38
    @9
    @27
    @38
    @7
    @8
    @38
    @7
    wph
    @35
    @37
    simplr
    rexrd
    #
    @36
    cA
    cxr
    @5
    cF
    wph
    cA
    cxr
    cF
    wf
    @35
    limsupre2lem.3
    adantr
    ffvelrnda
    #
    xrltnled
    bicomd
    anbi2d
    rexbidva
    ralbidv
    rexbidva
    bitrd
    3bitrd
    wph
    @3
    @0
    cpnf
    wceq
    #
    wn
    #
    @6
    @7
    @8
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
    wn
    #
    @18
    @3
    @42
    wb
    wph
    @0
    cpnf
    df-ne
    a1i
    wph
    @41
    @47
    wph
    vx
    cA
    vj
    vk
    cF
    limsupre2lem.1
    limsupre2lem.2
    limsupre2lem.3
    limsuppnf
    notbid
    wph
    @18
    @6
    @43
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
    @48
    wph
    @17
    @52
    vx
    cr
    @36
    @16
    @51
    vk
    cr
    @36
    @15
    @50
    vj
    cA
    @38
    @14
    @49
    @6
    @38
    @8
    @7
    @40
    @39
    xrltnled
    imbi2d
    ralbidva
    rexbidv
    rexbidva
    @53
    @48
    wb
    wph
    @53
    @46
    wn
    #
    vx
    cr
    wrex
    @48
    @52
    @54
    vx
    cr
    @52
    @45
    wn
    #
    vk
    cr
    wrex
    @54
    @51
    @55
    vk
    cr
    @51
    @44
    wn
    #
    vj
    cA
    wral
    @55
    @50
    @56
    vj
    cA
    @6
    @43
    imnan
    ralbii
    @44
    vj
    cA
    ralnex
    bitri
    rexbii
    @45
    vk
    cr
    rexnal
    bitri
    rexbii
    @46
    vx
    cr
    rexnal
    bitri
    a1i
    bitr2d
    3bitrd
    anbi12d
    bitrd
end

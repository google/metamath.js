include "clsp.mm"
include "cfv.mm"
include "cmnf.mm"
include "wceq.mm"
include "cr.mm"
include "cv.mm"
include "cpnf.mm"
include "cico.mm"
include "co.mm"
include "cima.mm"
include "cxr.mm"
include "clt.mm"
include "csup.mm"
include "cmpt.mm"
include "crn.mm"
include "cinf.mm"
include "cle.mm"
include "wbr.mm"
include "wrex.mm"
include "wral.mm"
include "wi.mm"
include "cvv.mm"
include "nfv.mm"
include "wcel.mm"
include "reex.mm"
include "a1i.mm"
include "ssexd.mm"
include "limsupval3.mm"
include "rneqi.mm"
include "infeq1i.mm"
include "eqtrd.mm"
include "eqeq1d.mm"
include "wa.mm"
include "wss.mm"
include "fimassd.mm"
include "adantr.mm"
include "supxrcld.mm"
include "infxrunb3rnmpt.mm"
include "wb.mm"
include "ressxr.mm"
include "sselda.mm"
include "supxrleub.mm"
include "syl2anc.mm"
include "wfn.mm"
include "ffnd.mm"
include "ad3antrrr.mm"
include "simplr.mm"
include "sseli.mm"
include "ad3antlr.mm"
include "pnfxr.mm"
include "sseldd.mm"
include "ad4ant13.mm"
include "simpr.mm"
include "ltpnfd.mm"
include "elicod.mm"
include "fnfvimad.mm"
include "adantllr.mm"
include "simpllr.mm"
include "breq1.mm"
include "rspcva.mm"
include "adantl4r.mm"
include "ex.mm"
include "ralrimiva.mm"
include "cin.mm"
include "nfcv.mm"
include "fvelimad.mm"
include "ad4ant14.mm"
include "nfra1.mm"
include "nfan.mm"
include "elinel2.mm"
include "adantl.mm"
include "icogelbd.mm"
include "adantlr.mm"
include "elinel1.mm"
include "rspa.mm"
include "syldan.mm"
include "adantll.mm"
include "mpd.mm"
include "id.mm"
include "eqcomd.mm"
include "simpl.mm"
include "eqbrtrd.mm"
include "syl.mm"
include "adantlll.mm"
include "rexlimd.mm"
include "imp.mm"
include "ad2antrr.mm"
include "mpbird.mm"
include "sylibd.mm"
include "impbid.mm"
include "bitrd.mm"
include "rexbidva.mm"
include "ralbidva.mm"
include "3bitr2d.mm"

theorem limsupmnflem
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let vj: setvar j
  let vk: setvar k
  let cF: class F
  let cG: class G
  let vy: setvar y
  assume limsupmnflem.a: |- ( ph -> A C_ RR )
  assume limsupmnflem.f: |- ( ph -> F : A --> RR* )
  assume limsupmnflem.g: |- G = ( k e. RR |-> sup ( ( F " ( k [,) +oo ) ) , RR* , < ) )

  disjoint A j
  disjoint F j
  disjoint F k
  disjoint F x
  disjoint j k
  disjoint j x
  disjoint k x
  disjoint j ph
  disjoint k ph
  disjoint ph x
  disjoint A y
  disjoint j y
  disjoint F y
  disjoint k y
  disjoint x y
  disjoint ph y
  assert |- ( ph -> ( ( limsup ` F ) = -oo <-> A. x e. RR E. k e. RR A. j e. A ( k <_ j -> ( F ` j ) <_ x ) ) )

  proof
    wph
    cF
    clsp
    cfv
    #
    cmnf
    wceq
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
    clt
    csup
    #
    cmpt
    #
    crn
    #
    cxr
    clt
    cinf
    #
    cmnf
    wceq
    @4
    vx
    cv
    #
    cle
    wbr
    #
    vk
    cr
    wrex
    #
    vx
    cr
    wral
    @1
    vj
    cv
    #
    cle
    wbr
    #
    @11
    cF
    cfv
    #
    @8
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
    wph
    @0
    @7
    cmnf
    wph
    @0
    cG
    crn
    #
    cxr
    clt
    cinf
    #
    @7
    wph
    cA
    vk
    cF
    cG
    cvv
    wph
    vk
    nfv
    #
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
    limsupmnflem.a
    ssexd
    limsupmnflem.f
    limsupmnflem.g
    limsupval3
    @19
    @7
    wceq
    wph
    cxr
    @18
    @6
    clt
    cG
    @5
    limsupmnflem.g
    rneqi
    infeq1i
    a1i
    eqtrd
    eqeq1d
    wph
    vk
    vx
    cr
    @4
    @20
    wph
    vx
    nfv
    wph
    @1
    cr
    wcel
    #
    wa
    #
    @3
    wph
    @3
    cxr
    wss
    #
    @21
    wph
    cA
    cxr
    cF
    @2
    limsupmnflem.f
    fimassd
    #
    adantr
    supxrcld
    infxrunb3rnmpt
    wph
    @10
    @17
    vx
    cr
    wph
    @8
    cr
    wcel
    #
    wa
    #
    @9
    @16
    vk
    cr
    @26
    @21
    wa
    #
    @9
    vy
    cv
    #
    @8
    cle
    wbr
    #
    vy
    @3
    wral
    #
    @16
    @26
    @9
    @30
    wb
    #
    @21
    @26
    @23
    @8
    cxr
    wcel
    @31
    wph
    @23
    @25
    @24
    adantr
    wph
    cr
    cxr
    @8
    cr
    cxr
    wss
    #
    wph
    ressxr
    a1i
    sselda
    vy
    @3
    @8
    supxrleub
    syl2anc
    #
    adantr
    #
    @27
    @30
    @16
    @27
    @30
    @16
    @27
    @30
    wa
    #
    @15
    vj
    cA
    @35
    @11
    cA
    wcel
    #
    wa
    @12
    @14
    wph
    @25
    @21
    @30
    @36
    @12
    @14
    @22
    @30
    wa
    @36
    wa
    @12
    wa
    @13
    @3
    wcel
    #
    @30
    @14
    @22
    @36
    @12
    @37
    @30
    @22
    @36
    wa
    #
    @12
    wa
    #
    cA
    @11
    @2
    cF
    wph
    cF
    cA
    wfn
    #
    @21
    @36
    @12
    wph
    cA
    cxr
    cF
    limsupmnflem.f
    ffnd
    #
    ad3antrrr
    @22
    @36
    @12
    simplr
    @39
    @1
    cpnf
    @11
    @21
    @1
    cxr
    wcel
    #
    wph
    @36
    @12
    cr
    cxr
    @1
    ressxr
    sseli
    #
    ad3antlr
    cpnf
    cxr
    wcel
    #
    @39
    pnfxr
    a1i
    wph
    @36
    @11
    cxr
    wcel
    @21
    @12
    wph
    @36
    wa
    #
    cr
    cxr
    @11
    @32
    @45
    ressxr
    a1i
    wph
    cA
    cr
    @11
    limsupmnflem.a
    sselda
    #
    sseldd
    ad4ant13
    @38
    @12
    simpr
    wph
    @36
    @11
    cpnf
    clt
    wbr
    @21
    @12
    @45
    @11
    @46
    ltpnfd
    ad4ant13
    elicod
    fnfvimad
    adantllr
    @22
    @30
    @36
    @12
    simpllr
    @29
    @14
    vy
    @13
    @3
    @28
    @13
    @8
    cle
    breq1
    rspcva
    syl2anc
    adantl4r
    ex
    ralrimiva
    ex
    @27
    @16
    @9
    @30
    @27
    @16
    @9
    @27
    @16
    wa
    @9
    @30
    wph
    @21
    @16
    @30
    @25
    @22
    @16
    wa
    #
    @29
    vy
    @3
    @47
    @28
    @3
    wcel
    #
    @13
    @28
    wceq
    #
    vj
    cA
    @2
    cin
    #
    wrex
    #
    @29
    wph
    @48
    @51
    @21
    @16
    wph
    @48
    wa
    vj
    cA
    @2
    @28
    cF
    vj
    cF
    nfcv
    wph
    @40
    @48
    @41
    adantr
    wph
    @48
    simpr
    fvelimad
    ad4ant14
    @47
    @51
    @29
    @47
    @49
    @29
    vj
    @50
    @22
    @16
    vj
    @22
    vj
    nfv
    @15
    vj
    cA
    nfra1
    nfan
    @29
    vj
    nfv
    @47
    @11
    @50
    wcel
    #
    @49
    @29
    wi
    #
    @21
    @16
    @52
    @53
    wph
    @21
    @16
    wa
    @52
    wa
    #
    @14
    @53
    @54
    @12
    @14
    @21
    @52
    @12
    @16
    @21
    @52
    wa
    #
    @1
    cpnf
    @11
    @21
    @42
    @52
    @43
    adantr
    @44
    @55
    pnfxr
    a1i
    @52
    @11
    @2
    wcel
    @21
    @11
    cA
    @2
    elinel2
    adantl
    icogelbd
    adantlr
    @16
    @52
    @15
    @21
    @16
    @52
    @36
    @15
    @52
    @36
    @16
    @11
    cA
    @2
    elinel1
    adantl
    @15
    vj
    cA
    rspa
    syldan
    adantll
    mpd
    @14
    @49
    @29
    @14
    @49
    wa
    @28
    @13
    @8
    cle
    @49
    @28
    @13
    wceq
    @14
    @49
    @13
    @28
    @49
    id
    eqcomd
    adantl
    @14
    @49
    simpl
    eqbrtrd
    ex
    syl
    adantlll
    ex
    rexlimd
    imp
    syldan
    ralrimiva
    adantllr
    @26
    @31
    @21
    @16
    @33
    ad2antrr
    mpbird
    ex
    @34
    sylibd
    impbid
    bitrd
    rexbidva
    ralbidva
    3bitr2d
end

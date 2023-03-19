include "cmnf.mm"
include "clsxlim.mm"
include "wbr.mm"
include "cv.mm"
include "cfv.mm"
include "cle.mm"
include "cuz.mm"
include "wral.mm"
include "wrex.mm"
include "cr.mm"
include "wa.mm"
include "wcel.mm"
include "cz.mm"
include "ad2antrr.mm"
include "cxr.mm"
include "wf.mm"
include "simplr.mm"
include "simpr.mm"
include "xlimmnfvlem1.mm"
include "ralrimiva.mm"
include "nfv.mm"
include "nfcv.mm"
include "nfra1.mm"
include "nfrex.mm"
include "nfral.mm"
include "nfan.mm"
include "nfre1.mm"
include "adantr.mm"
include "clt.mm"
include "c1.mm"
include "cmin.mm"
include "co.mm"
include "w3a.mm"
include "3ad2ant1.mm"
include "uztrn2.mm"
include "3adant1.mm"
include "ffvelrnd.mm"
include "ad5ant134.mm"
include "simp-4r.mm"
include "peano2rem.mm"
include "rexrd.mm"
include "syl.mm"
include "rexr.mm"
include "ad4antlr.mm"
include "ltm1d.mm"
include "xrlelttrd.mm"
include "ex.mm"
include "ralimdva.mm"
include "imp.mm"
include "ad5ant1345.mm"
include "3impa.mm"
include "adantl.mm"
include "simpl.mm"
include "wceq.mm"
include "breq2.mm"
include "ralbidv.mm"
include "rexbidv.mm"
include "rspcva.mm"
include "syl2anc.mm"
include "adantll.mm"
include "reximdd.mm"
include "xlimmnfvlem2.mm"
include "impbida.mm"

theorem xlimmnfv
  let wph: wff ph
  let vx: setvar x
  let vj: setvar j
  let vk: setvar k
  let cF: class F
  let cM: class M
  let cZ: class Z
  let vy: setvar y
  assume xlimmnfv.m: |- ( ph -> M e. ZZ )
  assume xlimmnfv.z: |- Z = ( ZZ>= ` M )
  assume xlimmnfv.f: |- ( ph -> F : Z --> RR* )

  disjoint F j
  disjoint F k
  disjoint F x
  disjoint j k
  disjoint j x
  disjoint k x
  disjoint M j
  disjoint Z j
  disjoint Z k
  disjoint Z x
  disjoint j ph
  disjoint k ph
  disjoint ph x
  disjoint k x
  disjoint F y
  disjoint j y
  disjoint k y
  disjoint x y
  disjoint Z y
  disjoint ph y
  assert |- ( ph -> ( F ~~>* -oo <-> A. x e. RR E. j e. Z A. k e. ( ZZ>= ` j ) ( F ` k ) <_ x ) )

  proof
    wph
    cF
    cmnf
    clsxlim
    wbr
    #
    vk
    cv
    #
    cF
    cfv
    #
    vx
    cv
    #
    cle
    wbr
    #
    vk
    vj
    cv
    #
    cuz
    cfv
    #
    wral
    #
    vj
    cZ
    wrex
    #
    vx
    cr
    wral
    #
    wph
    @0
    wa
    #
    @8
    vx
    cr
    @10
    @3
    cr
    wcel
    #
    wa
    vj
    vk
    cF
    cM
    @3
    cZ
    wph
    cM
    cz
    wcel
    #
    @0
    @11
    xlimmnfv.m
    ad2antrr
    xlimmnfv.z
    wph
    cZ
    cxr
    cF
    wf
    #
    @0
    @11
    xlimmnfv.f
    ad2antrr
    wph
    @0
    @11
    simplr
    @10
    @11
    simpr
    xlimmnfvlem1
    ralrimiva
    wph
    @9
    wa
    #
    vy
    vj
    vk
    cF
    cM
    cZ
    wph
    @9
    vk
    wph
    vk
    nfv
    @8
    vk
    vx
    cr
    vk
    cr
    nfcv
    @7
    vk
    vj
    cZ
    vk
    cZ
    nfcv
    @4
    vk
    @6
    nfra1
    nfrex
    nfral
    nfan
    wph
    @9
    vj
    wph
    vj
    nfv
    @8
    vj
    vx
    cr
    vj
    cr
    nfcv
    @7
    vj
    cZ
    nfre1
    nfral
    nfan
    #
    wph
    @12
    @9
    xlimmnfv.m
    adantr
    xlimmnfv.z
    wph
    @13
    @9
    xlimmnfv.f
    adantr
    @14
    @2
    vy
    cv
    #
    clt
    wbr
    #
    vk
    @6
    wral
    #
    vj
    cZ
    wrex
    vy
    cr
    @14
    @16
    cr
    wcel
    #
    wa
    #
    @2
    @16
    c1
    cmin
    co
    #
    cle
    wbr
    #
    vk
    @6
    wral
    #
    @18
    vj
    cZ
    @14
    @19
    vj
    @15
    @19
    vj
    nfv
    nfan
    @20
    @5
    cZ
    wcel
    #
    @23
    @18
    wph
    @19
    @24
    @23
    @18
    @9
    wph
    @19
    wa
    @24
    wa
    #
    @23
    @18
    @25
    @22
    @17
    vk
    @6
    @25
    @1
    @6
    wcel
    #
    wa
    #
    @22
    @17
    @27
    @22
    wa
    #
    @2
    @21
    @16
    wph
    @24
    @26
    @2
    cxr
    wcel
    @19
    @22
    wph
    @24
    @26
    w3a
    cZ
    cxr
    @1
    cF
    wph
    @24
    @13
    @26
    xlimmnfv.f
    3ad2ant1
    @24
    @26
    @1
    cZ
    wcel
    wph
    cM
    @1
    @5
    cZ
    xlimmnfv.z
    uztrn2
    3adant1
    ffvelrnd
    ad5ant134
    @28
    @19
    @21
    cxr
    wcel
    wph
    @19
    @24
    @26
    @22
    simp-4r
    #
    @19
    @21
    @16
    peano2rem
    #
    rexrd
    syl
    @19
    @16
    cxr
    wcel
    wph
    @24
    @26
    @22
    @16
    rexr
    ad4antlr
    @27
    @22
    simpr
    @28
    @16
    @29
    ltm1d
    xrlelttrd
    ex
    ralimdva
    imp
    ad5ant1345
    3impa
    @9
    @19
    @23
    vj
    cZ
    wrex
    #
    wph
    @9
    @19
    wa
    @21
    cr
    wcel
    #
    @9
    @31
    @19
    @32
    @9
    @30
    adantl
    @9
    @19
    simpl
    @8
    @31
    vx
    @21
    cr
    @3
    @21
    wceq
    #
    @7
    @23
    vj
    cZ
    @33
    @4
    @22
    vk
    @6
    @3
    @21
    @2
    cle
    breq2
    ralbidv
    rexbidv
    rspcva
    syl2anc
    adantll
    reximdd
    ralrimiva
    xlimmnfvlem2
    impbida
end

include "clsp.mm"
include "cfv.mm"
include "cr.mm"
include "wcel.mm"
include "cv.mm"
include "cle.mm"
include "wbr.mm"
include "clt.mm"
include "wa.mm"
include "wrex.mm"
include "wral.mm"
include "wi.mm"
include "limsupre2.mm"
include "w3a.mm"
include "simp2.mm"
include "nfv.mm"
include "simp3l.mm"
include "simp1r.mm"
include "rexrd.mm"
include "cxr.mm"
include "ffvelrnda.mm"
include "adantlr.mm"
include "3adant3.mm"
include "simp3.mm"
include "xrltled.mm"
include "3adant3l.mm"
include "jca.mm"
include "3exp.mm"
include "reximdai.mm"
include "ralimdv.mm"
include "3impia.mm"
include "wceq.mm"
include "breq1.mm"
include "anbi2d.mm"
include "rexbidv.mm"
include "ralbidv.mm"
include "rspcev.mm"
include "syl2anc.mm"
include "rexlimdv.mm"
include "c1.mm"
include "cmin.mm"
include "co.mm"
include "peano2rem.mm"
include "ad2antlr.mm"
include "syl.mm"
include "ltm1d.mm"
include "simp3r.mm"
include "xrltletrd.mm"
include "imp.mm"
include "ex.mm"
include "rexlimdva.mm"
include "impbid.mm"
include "simplr.mm"
include "adantr.mm"
include "rexr.mm"
include "ad3antlr.mm"
include "simpr.mm"
include "imim2d.mm"
include "ralimdva.mm"
include "reximdv.mm"
include "breq2.mm"
include "imbi2d.mm"
include "caddc.mm"
include "peano2re.mm"
include "ltp1.mm"
include "xrlelttrd.mm"
include "anbi12d.mm"
include "bitrd.mm"

theorem limsupre3lem
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let vj: setvar j
  let vk: setvar k
  let cF: class F
  let vy: setvar y
  assume limsupre3lem.1: |- F/_ j F
  assume limsupre3lem.2: |- ( ph -> A C_ RR )
  assume limsupre3lem.3: |- ( ph -> F : A --> RR* )

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
  disjoint A y
  disjoint j y
  disjoint k y
  disjoint x y
  disjoint F y
  disjoint ph y
  assert |- ( ph -> ( ( limsup ` F ) e. RR <-> ( E. x e. RR A. k e. RR E. j e. A ( k <_ j /\ x <_ ( F ` j ) ) /\ E. x e. RR E. k e. RR A. j e. A ( k <_ j -> ( F ` j ) <_ x ) ) ) )

  proof
    wph
    cF
    clsp
    cfv
    cr
    wcel
    vk
    cv
    vj
    cv
    #
    cle
    wbr
    #
    vy
    cv
    #
    @0
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
    vy
    cr
    wrex
    #
    @1
    @3
    @2
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
    vy
    cr
    wrex
    #
    wa
    @1
    vx
    cv
    #
    @3
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
    wrex
    #
    @1
    @3
    @14
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
    wa
    wph
    vy
    cA
    vj
    vk
    cF
    limsupre3lem.1
    limsupre3lem.2
    limsupre3lem.3
    limsupre2
    wph
    @8
    @19
    @13
    @24
    wph
    @8
    @19
    wph
    @7
    @19
    vy
    cr
    wph
    @2
    cr
    wcel
    #
    @7
    @19
    wph
    @25
    @7
    w3a
    @25
    @1
    @2
    @3
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
    @19
    wph
    @25
    @7
    simp2
    wph
    @25
    @7
    @29
    wph
    @25
    wa
    #
    @6
    @28
    vk
    cr
    @30
    @5
    @27
    vj
    cA
    @30
    vj
    nfv
    @30
    @0
    cA
    wcel
    #
    @5
    @27
    @30
    @31
    @5
    w3a
    @1
    @26
    @30
    @31
    @1
    @4
    simp3l
    @30
    @31
    @4
    @26
    @1
    @30
    @31
    @4
    w3a
    #
    @2
    @3
    @32
    @2
    wph
    @25
    @31
    @4
    simp1r
    rexrd
    @30
    @31
    @3
    cxr
    wcel
    #
    @4
    wph
    @31
    @33
    @25
    wph
    cA
    cxr
    @0
    cF
    limsupre3lem.3
    ffvelrnda
    #
    adantlr
    #
    3adant3
    @30
    @31
    @4
    simp3
    xrltled
    3adant3l
    jca
    3exp
    reximdai
    ralimdv
    3impia
    @18
    @29
    vx
    @2
    cr
    @14
    @2
    wceq
    #
    @17
    @28
    vk
    cr
    @36
    @16
    @27
    vj
    cA
    @36
    @15
    @26
    @1
    @14
    @2
    @3
    cle
    breq1
    anbi2d
    rexbidv
    ralbidv
    rspcev
    syl2anc
    3exp
    rexlimdv
    wph
    @18
    @8
    vx
    cr
    wph
    @14
    cr
    wcel
    #
    wa
    #
    @18
    @8
    @38
    @18
    wa
    @14
    c1
    cmin
    co
    #
    cr
    wcel
    #
    @1
    @39
    @3
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
    @8
    @37
    @40
    wph
    @18
    @14
    peano2rem
    #
    ad2antlr
    @38
    @18
    @44
    @38
    @17
    @43
    vk
    cr
    @38
    @16
    @42
    vj
    cA
    @38
    vj
    nfv
    @38
    @31
    @16
    @42
    @38
    @31
    @16
    w3a
    #
    @1
    @41
    @38
    @31
    @1
    @15
    simp3l
    @46
    @39
    @14
    @3
    @46
    @37
    @39
    cxr
    wcel
    wph
    @37
    @31
    @16
    simp1r
    #
    @37
    @39
    @45
    rexrd
    syl
    @46
    @14
    @47
    rexrd
    @38
    @31
    @33
    @16
    wph
    @31
    @33
    @37
    @34
    adantlr
    #
    3adant3
    @46
    @14
    @47
    ltm1d
    @38
    @31
    @1
    @15
    simp3r
    xrltletrd
    jca
    3exp
    reximdai
    ralimdv
    imp
    @7
    @44
    vy
    @39
    cr
    @2
    @39
    wceq
    #
    @6
    @43
    vk
    cr
    @49
    @5
    @42
    vj
    cA
    @49
    @4
    @41
    @1
    @2
    @39
    @3
    clt
    breq1
    anbi2d
    rexbidv
    ralbidv
    rspcev
    syl2anc
    ex
    rexlimdva
    impbid
    wph
    @13
    @24
    wph
    @12
    @24
    vy
    cr
    @30
    @12
    @24
    @30
    @12
    wa
    @25
    @1
    @3
    @2
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
    @24
    wph
    @25
    @12
    simplr
    @30
    @12
    @53
    @30
    @11
    @52
    vk
    cr
    @30
    @10
    @51
    vj
    cA
    @30
    @31
    wa
    #
    @9
    @50
    @1
    @54
    @9
    @50
    @54
    @9
    wa
    @3
    @2
    @54
    @33
    @9
    @35
    adantr
    @25
    @2
    cxr
    wcel
    wph
    @31
    @9
    @2
    rexr
    ad3antlr
    @54
    @9
    simpr
    xrltled
    ex
    imim2d
    ralimdva
    reximdv
    imp
    @23
    @53
    vx
    @2
    cr
    @36
    @22
    @52
    vk
    cr
    @36
    @21
    @51
    vj
    cA
    @36
    @20
    @50
    @1
    @14
    @2
    @3
    cle
    breq2
    imbi2d
    ralbidv
    rexbidv
    rspcev
    syl2anc
    ex
    rexlimdva
    wph
    @23
    @13
    vx
    cr
    @38
    @23
    @13
    @38
    @23
    wa
    @14
    c1
    caddc
    co
    #
    cr
    wcel
    #
    @1
    @3
    @55
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
    @13
    @37
    @56
    wph
    @23
    @14
    peano2re
    #
    ad2antlr
    @38
    @23
    @60
    @38
    @22
    @59
    vk
    cr
    @38
    @21
    @58
    vj
    cA
    @38
    @31
    wa
    #
    @20
    @57
    @1
    @62
    @20
    @57
    @62
    @20
    wa
    @3
    @14
    @55
    @62
    @33
    @20
    @48
    adantr
    @37
    @14
    cxr
    wcel
    wph
    @31
    @20
    @14
    rexr
    ad3antlr
    @37
    @55
    cxr
    wcel
    wph
    @31
    @20
    @37
    @55
    @61
    rexrd
    ad3antlr
    @62
    @20
    simpr
    @37
    @14
    @55
    clt
    wbr
    wph
    @31
    @20
    @14
    ltp1
    ad3antlr
    xrlelttrd
    ex
    imim2d
    ralimdva
    reximdv
    imp
    @12
    @60
    vy
    @55
    cr
    @2
    @55
    wceq
    #
    @11
    @59
    vk
    cr
    @63
    @10
    @58
    vj
    cA
    @63
    @9
    @57
    @1
    @2
    @55
    @3
    clt
    breq2
    imbi2d
    ralbidv
    rexbidv
    rspcev
    syl2anc
    ex
    rexlimdva
    impbid
    anbi12d
    bitrd
end

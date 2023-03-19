include "crg.mm"
include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "cco1.mm"
include "cfv.mm"
include "wceq.mm"
include "cn.mm"
include "wral.mm"
include "co.mm"
include "cc0.mm"
include "cfz.mm"
include "cmin.mm"
include "cmulr.mm"
include "cmpt.mm"
include "cgsu.mm"
include "cn0.mm"
include "cvv.mm"
include "eqid.mm"
include "coe1mul.mm"
include "3expb.mm"
include "adantr.mm"
include "weq.mm"
include "oveq2.mm"
include "oveq1.mm"
include "fveq2d.mm"
include "oveq2d.mm"
include "mpteq12dv.mm"
include "adantl.mm"
include "nnnn0.mm"
include "ovexd.mm"
include "fvmptd.mm"
include "wi.mm"
include "r19.26.mm"
include "nncn.mm"
include "subid1d.mm"
include "sylan9eqr.mm"
include "simpll.mm"
include "eqeltrd.mm"
include "fveq2.mm"
include "eqeq1d.mm"
include "rspcv.mm"
include "syl.mm"
include "cbs.mm"
include "simpl.mm"
include "elfznn0.mm"
include "coe1fvalcl.mm"
include "syl2an.mm"
include "ringrz.mm"
include "syl2anc.mm"
include "ex.mm"
include "expcom.mm"
include "com23.mm"
include "syldc.mm"
include "expd.mm"
include "com24.mm"
include "com13.mm"
include "wn.mm"
include "wne.mm"
include "df-ne.mm"
include "biimpri.mm"
include "anim12ci.mm"
include "elnnne0.mm"
include "sylibr.mm"
include "eleq2i.mm"
include "biimpi.mm"
include "fznn0sub.mm"
include "ringlz.mm"
include "a1dd.mm"
include "com14.mm"
include "syld.mm"
include "imp.mm"
include "pm2.61i.mm"
include "syl5bi.mm"
include "impl.mm"
include "mpteq2dva.mm"
include "cmnd.mm"
include "ringmnd.mm"
include "gsumz.mm"
include "3eqtrd.mm"
include "ralrimiva.mm"
include "cbvralv.mm"

theorem cply1mul
  let cB: class B
  let cP: class P
  let cR: class R
  let c.xp: class .X.
  let cF: class F
  let cG: class G
  let c.0: class .0.
  let vc: setvar c
  let vk: setvar k
  let vn: setvar n
  let vs: setvar s
  assume cply1mul.p: |- P = ( Poly1 ` R )
  assume cply1mul.b: |- B = ( Base ` P )
  assume cply1mul.0: |- .0. = ( 0g ` R )
  assume cply1mul.m: |- .X. = ( .r ` P )

  disjoint F c
  disjoint G c
  disjoint .X. c
  disjoint .0. c
  disjoint B k
  disjoint B n
  disjoint B s
  disjoint k n
  disjoint k s
  disjoint n s
  disjoint F k
  disjoint F n
  disjoint F s
  disjoint c k
  disjoint c n
  disjoint c s
  disjoint G k
  disjoint G n
  disjoint G s
  disjoint R k
  disjoint R n
  disjoint R s
  disjoint .X. n
  disjoint .X. s
  disjoint .0. k
  disjoint .0. n
  disjoint .0. s
  assert |- ( ( R e. Ring /\ ( F e. B /\ G e. B ) ) -> ( A. c e. NN ( ( ( coe1 ` F ) ` c ) = .0. /\ ( ( coe1 ` G ) ` c ) = .0. ) -> A. c e. NN ( ( coe1 ` ( F .X. G ) ) ` c ) = .0. ) )

  proof
    cR
    crg
    wcel
    #
    cF
    cB
    wcel
    #
    cG
    cB
    wcel
    #
    wa
    #
    wa
    #
    vc
    cv
    #
    cF
    cco1
    cfv
    #
    cfv
    #
    c.0
    wceq
    #
    @5
    cG
    cco1
    cfv
    #
    cfv
    #
    c.0
    wceq
    #
    wa
    vc
    cn
    wral
    #
    @5
    cF
    cG
    c.xp
    co
    cco1
    cfv
    #
    cfv
    #
    c.0
    wceq
    #
    vc
    cn
    wral
    #
    @4
    @12
    wa
    #
    vn
    cv
    #
    @13
    cfv
    #
    c.0
    wceq
    #
    vn
    cn
    wral
    @16
    @17
    @20
    vn
    cn
    @17
    @18
    cn
    wcel
    #
    wa
    #
    @19
    cR
    vk
    cc0
    @18
    cfz
    co
    #
    vk
    cv
    #
    @6
    cfv
    #
    @18
    @24
    cmin
    co
    #
    @9
    cfv
    #
    cR
    cmulr
    cfv
    #
    co
    #
    cmpt
    #
    cgsu
    co
    #
    cR
    vk
    @23
    c.0
    cmpt
    #
    cgsu
    co
    #
    c.0
    @22
    vs
    @18
    cR
    vk
    cc0
    vs
    cv
    #
    cfz
    co
    #
    @25
    @34
    @24
    cmin
    co
    #
    @9
    cfv
    #
    @28
    co
    #
    cmpt
    #
    cgsu
    co
    #
    @31
    cn0
    @13
    cvv
    @17
    @13
    vs
    cn0
    @40
    cmpt
    wceq
    #
    @21
    @4
    @41
    @12
    @0
    @1
    @2
    @41
    vk
    cB
    cR
    c.xp
    @28
    vs
    cF
    cG
    cP
    cply1mul.p
    cply1mul.m
    @28
    eqid
    #
    cply1mul.b
    coe1mul
    3expb
    adantr
    adantr
    vs
    vn
    weq
    #
    @40
    @31
    wceq
    @22
    @43
    @39
    @30
    cR
    cgsu
    @43
    vk
    @35
    @38
    @23
    @29
    @34
    @18
    cc0
    cfz
    oveq2
    @43
    @37
    @27
    @25
    @28
    @43
    @36
    @26
    @9
    @34
    @18
    @24
    cmin
    oveq1
    fveq2d
    oveq2d
    mpteq12dv
    oveq2d
    adantl
    @21
    @18
    cn0
    wcel
    @17
    @18
    nnnn0
    adantl
    @22
    cR
    @30
    cgsu
    ovexd
    fvmptd
    @22
    @30
    @32
    cR
    cgsu
    @22
    vk
    @23
    @29
    c.0
    @17
    @21
    @24
    @23
    wcel
    #
    @29
    c.0
    wceq
    #
    @4
    @12
    @21
    @44
    wa
    #
    @45
    wi
    #
    @12
    @8
    vc
    cn
    wral
    #
    @11
    vc
    cn
    wral
    #
    wa
    #
    @4
    @47
    @8
    @11
    vc
    cn
    r19.26
    @24
    cc0
    wceq
    #
    @4
    @50
    @47
    wi
    wi
    @50
    @4
    @51
    @47
    @49
    @4
    @51
    @47
    wi
    wi
    @48
    @49
    @46
    @51
    @4
    @45
    @49
    @46
    @51
    @4
    @45
    wi
    #
    @46
    @51
    wa
    #
    @49
    @27
    c.0
    wceq
    #
    @52
    @53
    @26
    cn
    wcel
    @49
    @54
    wi
    @53
    @26
    @18
    cn
    @51
    @46
    @26
    @18
    cc0
    cmin
    co
    #
    @18
    @24
    cc0
    @18
    cmin
    oveq2
    @21
    @55
    @18
    wceq
    @44
    @21
    @18
    @18
    nncn
    subid1d
    adantr
    sylan9eqr
    @21
    @44
    @51
    simpll
    eqeltrd
    @11
    @54
    vc
    @26
    cn
    @5
    @26
    wceq
    @10
    @27
    c.0
    @5
    @26
    @9
    fveq2
    eqeq1d
    rspcv
    syl
    @53
    @4
    @54
    @45
    @4
    @53
    @54
    @45
    wi
    @4
    @53
    wa
    #
    @54
    @45
    @54
    @56
    @29
    @25
    c.0
    @28
    co
    #
    c.0
    @27
    c.0
    @25
    @28
    oveq2
    @56
    @0
    @25
    cR
    cbs
    cfv
    #
    wcel
    #
    @57
    c.0
    wceq
    @0
    @3
    @53
    simpll
    @4
    @1
    @24
    cn0
    wcel
    #
    @59
    @53
    @3
    @1
    @0
    @1
    @2
    simpl
    adantl
    @46
    @60
    @51
    @44
    @60
    @21
    @24
    @18
    elfznn0
    #
    adantl
    adantr
    @6
    cB
    cP
    cR
    cF
    @58
    @24
    @6
    eqid
    cply1mul.b
    cply1mul.p
    @58
    eqid
    #
    coe1fvalcl
    syl2an
    @58
    cR
    @28
    @25
    c.0
    @62
    @42
    cply1mul.0
    ringrz
    syl2anc
    sylan9eqr
    ex
    expcom
    com23
    syldc
    expd
    com24
    adantl
    com13
    @50
    @4
    @51
    wn
    #
    @47
    @48
    @4
    @63
    @47
    wi
    wi
    @49
    @46
    @4
    @63
    @48
    @45
    @21
    @44
    @4
    @63
    @48
    @45
    wi
    #
    wi
    wi
    @63
    @44
    @4
    @21
    @64
    @63
    @44
    @4
    @21
    @64
    wi
    wi
    @63
    @44
    wa
    #
    @48
    @21
    @4
    @45
    @65
    @48
    @25
    c.0
    wceq
    #
    @21
    @52
    wi
    #
    @65
    @24
    cn
    wcel
    #
    @48
    @66
    wi
    @65
    @60
    @24
    cc0
    wne
    #
    wa
    @68
    @63
    @69
    @44
    @60
    @69
    @63
    @24
    cc0
    df-ne
    biimpri
    @61
    anim12ci
    @24
    elnnne0
    sylibr
    @8
    @66
    vc
    @24
    cn
    vc
    vk
    weq
    @7
    @25
    c.0
    @5
    @24
    @6
    fveq2
    eqeq1d
    rspcv
    syl
    @44
    @66
    @67
    wi
    @63
    @4
    @66
    @21
    @44
    @45
    @4
    @66
    @44
    @45
    wi
    @21
    @4
    @44
    @66
    @45
    @4
    @44
    @66
    @45
    wi
    @4
    @44
    wa
    #
    @66
    @45
    @66
    @70
    @29
    c.0
    @27
    @28
    co
    #
    c.0
    @25
    c.0
    @27
    @28
    oveq1
    @70
    @0
    @27
    @58
    wcel
    #
    @71
    c.0
    wceq
    @0
    @3
    @44
    simpll
    @4
    cG
    cP
    cbs
    cfv
    #
    wcel
    #
    @26
    cn0
    wcel
    @72
    @44
    @3
    @74
    @0
    @2
    @74
    @1
    @2
    @74
    cB
    @73
    cG
    cply1mul.b
    eleq2i
    biimpi
    adantl
    adantl
    @24
    cc0
    @18
    fznn0sub
    @9
    @73
    cP
    cR
    cG
    @58
    @26
    @9
    eqid
    @73
    eqid
    cply1mul.p
    @62
    coe1fvalcl
    syl2an
    @58
    cR
    @28
    @27
    c.0
    @62
    @42
    cply1mul.0
    ringlz
    syl2anc
    sylan9eqr
    ex
    ex
    com23
    a1dd
    com14
    adantl
    syld
    com24
    ex
    com14
    imp
    com14
    adantr
    com13
    pm2.61i
    syl5bi
    imp
    impl
    mpteq2dva
    oveq2d
    @17
    @33
    c.0
    wceq
    #
    @21
    @4
    @75
    @12
    @0
    @75
    @3
    @0
    cR
    cmnd
    wcel
    @23
    cvv
    wcel
    @75
    cR
    ringmnd
    @0
    cc0
    @18
    cfz
    ovexd
    @23
    vk
    cR
    cvv
    c.0
    cply1mul.0
    gsumz
    syl2anc
    adantr
    adantr
    adantr
    3eqtrd
    ralrimiva
    @15
    @20
    vc
    vn
    cn
    vc
    vn
    weq
    @14
    @19
    c.0
    @5
    @18
    @13
    fveq2
    eqeq1d
    cbvralv
    sylibr
    ex
end

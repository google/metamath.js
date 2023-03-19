include "cca.mm"
include "cfv.mm"
include "wcel.mm"
include "cc.mm"
include "cpm.mm"
include "co.mm"
include "cv.mm"
include "cdm.mm"
include "clt.mm"
include "wbr.mm"
include "w3a.mm"
include "cuz.mm"
include "wral.mm"
include "wrex.mm"
include "crp.mm"
include "wa.mm"
include "iscau3.mm"
include "wi.mm"
include "cz.mm"
include "simpr.mm"
include "syl6eleq.mm"
include "eluzelz.mm"
include "uzid.mm"
include "3syl.mm"
include "wceq.mm"
include "fveq2.mm"
include "oveq1d.mm"
include "breq1d.mm"
include "raleqbidv.mm"
include "rspcv.mm"
include "syl.mm"
include "adantr.mm"
include "oveq2d.mm"
include "cbvralv.mm"
include "ralimi.mm"
include "eleq1d.mm"
include "syl2im.mm"
include "imp.mm"
include "r19.26.mm"
include "cxmt.mm"
include "ad3antrrr.mm"
include "simplr.mm"
include "simprr.mm"
include "xmetsym.mm"
include "syl3anc.mm"
include "biimpd.mm"
include "expimpd.mm"
include "ralimdv.mm"
include "syl5bir.mm"
include "expd.mm"
include "impancom.mm"
include "mpd.mm"
include "syl5bi.mm"
include "syld.mm"
include "imdistanda.mm"
include "3imtr4g.mm"
include "df-3an.mm"
include "ralbii.mm"
include "reximdva.mm"
include "anim2d.mm"
include "sylbid.mm"
include "wss.mm"
include "uzssz.mm"
include "eqsstri.mm"
include "ssrexv.mm"
include "ax-mp.mm"
include "anim2i.mm"
include "iscau2.mm"
include "syl5ibr.mm"
include "impbid.mm"
include "wb.mm"
include "simpl.mm"
include "uztrn2.mm"
include "jca.mm"
include "adantrl.mm"
include "adantrr.mm"
include "oveq12d.mm"
include "3anbi23d.mm"
include "sylan2.mm"
include "anassrs.mm"
include "ralbidva.mm"
include "rexbidva.mm"
include "ralbidv.mm"
include "anbi2d.mm"
include "bitrd.mm"

theorem iscau4
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cD: class D
  let vj: setvar j
  let vk: setvar k
  let cF: class F
  let cM: class M
  let cX: class X
  let cZ: class Z
  let vd: setvar d
  let vf: setvar f
  let vm: setvar m
  assume iscau3.2: |- Z = ( ZZ>= ` M )
  assume iscau3.3: |- ( ph -> D e. ( *Met ` X ) )
  assume iscau3.4: |- ( ph -> M e. ZZ )
  assume iscau4.5: |- ( ( ph /\ k e. Z ) -> ( F ` k ) = A )
  assume iscau4.6: |- ( ( ph /\ j e. Z ) -> ( F ` j ) = B )

  disjoint j k
  disjoint j x
  disjoint D j
  disjoint k x
  disjoint D k
  disjoint D x
  disjoint F j
  disjoint F k
  disjoint F x
  disjoint j ph
  disjoint k ph
  disjoint ph x
  disjoint X j
  disjoint X k
  disjoint X x
  disjoint M j
  disjoint Z j
  disjoint Z k
  disjoint Z x
  disjoint d f
  disjoint d j
  disjoint d k
  disjoint d m
  disjoint d x
  disjoint D d
  disjoint f j
  disjoint f k
  disjoint f m
  disjoint f x
  disjoint D f
  disjoint j m
  disjoint k m
  disjoint m x
  disjoint D m
  disjoint F f
  disjoint F m
  disjoint X d
  disjoint X f
  disjoint X m
  disjoint Z m
  assert |- ( ph -> ( F e. ( Cau ` D ) <-> ( F e. ( X ^pm CC ) /\ A. x e. RR+ E. j e. Z A. k e. ( ZZ>= ` j ) ( k e. dom F /\ A e. X /\ ( A D B ) < x ) ) ) )

  proof
    wph
    cF
    cD
    cca
    cfv
    wcel
    #
    cF
    cX
    cc
    cpm
    co
    wcel
    #
    vk
    cv
    #
    cF
    cdm
    wcel
    #
    @2
    cF
    cfv
    #
    cX
    wcel
    #
    @4
    vj
    cv
    #
    cF
    cfv
    #
    cD
    co
    #
    vx
    cv
    #
    clt
    wbr
    #
    w3a
    #
    vk
    @6
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
    crp
    wral
    #
    wa
    #
    @1
    @3
    cA
    cX
    wcel
    #
    cA
    cB
    cD
    co
    #
    @9
    clt
    wbr
    #
    w3a
    #
    vk
    @12
    wral
    #
    vj
    cZ
    wrex
    #
    vx
    crp
    wral
    #
    wa
    wph
    @0
    @16
    wph
    @0
    @1
    @3
    @5
    @4
    vm
    cv
    #
    cF
    cfv
    #
    cD
    co
    #
    @9
    clt
    wbr
    #
    vm
    @2
    cuz
    cfv
    #
    wral
    #
    w3a
    #
    vk
    @12
    wral
    #
    vj
    cZ
    wrex
    #
    vx
    crp
    wral
    #
    wa
    @16
    wph
    vx
    cD
    vj
    vk
    vm
    cF
    cM
    cX
    cZ
    iscau3.2
    iscau3.3
    iscau3.4
    iscau3
    wph
    @33
    @15
    @1
    wph
    @32
    @14
    vx
    crp
    wph
    @31
    @13
    vj
    cZ
    wph
    @6
    cZ
    wcel
    #
    wa
    #
    @3
    @5
    wa
    #
    @29
    wa
    #
    vk
    @12
    wral
    #
    @36
    @10
    wa
    #
    vk
    @12
    wral
    #
    @31
    @13
    @35
    @36
    vk
    @12
    wral
    #
    @29
    vk
    @12
    wral
    #
    wa
    @41
    @10
    vk
    @12
    wral
    #
    wa
    @38
    @40
    @35
    @41
    @42
    @43
    @35
    @41
    wa
    #
    @42
    @7
    @25
    cD
    co
    #
    @9
    clt
    wbr
    #
    vm
    @12
    wral
    #
    @43
    @35
    @42
    @47
    wi
    #
    @41
    @35
    @6
    @12
    wcel
    #
    @48
    @35
    @6
    cM
    cuz
    cfv
    #
    wcel
    @6
    cz
    wcel
    @49
    @35
    @6
    cZ
    @50
    wph
    @34
    simpr
    iscau3.2
    syl6eleq
    cM
    @6
    eluzelz
    @6
    uzid
    3syl
    #
    @29
    @47
    vk
    @6
    @12
    @2
    @6
    wceq
    #
    @27
    @46
    vm
    @28
    @12
    @2
    @6
    cuz
    fveq2
    @52
    @26
    @45
    @9
    clt
    @52
    @4
    @7
    @25
    cD
    @2
    @6
    cF
    fveq2
    #
    oveq1d
    breq1d
    raleqbidv
    rspcv
    syl
    adantr
    @47
    @7
    @4
    cD
    co
    #
    @9
    clt
    wbr
    #
    vk
    @12
    wral
    #
    @44
    @43
    @46
    @55
    vm
    vk
    @12
    @24
    @2
    wceq
    #
    @45
    @54
    @9
    clt
    @57
    @25
    @4
    @7
    cD
    @24
    @2
    cF
    fveq2
    oveq2d
    breq1d
    cbvralv
    @44
    @7
    cX
    wcel
    #
    @56
    @43
    wi
    #
    @35
    @41
    @58
    @35
    @49
    @41
    @5
    vk
    @12
    wral
    @58
    @51
    @36
    @5
    vk
    @12
    @3
    @5
    simpr
    ralimi
    @5
    @58
    vk
    @6
    @12
    @52
    @4
    @7
    cX
    @53
    eleq1d
    rspcv
    syl2im
    imp
    @35
    @58
    @41
    @59
    @35
    @58
    wa
    #
    @41
    @56
    @43
    @41
    @56
    wa
    @36
    @55
    wa
    #
    vk
    @12
    wral
    @60
    @43
    @36
    @55
    vk
    @12
    r19.26
    @60
    @61
    @10
    vk
    @12
    @60
    @36
    @55
    @10
    @60
    @36
    wa
    #
    @55
    @10
    @62
    @54
    @8
    @9
    clt
    @62
    cD
    cX
    cxmt
    cfv
    wcel
    #
    @58
    @5
    @54
    @8
    wceq
    wph
    @63
    @34
    @58
    @36
    iscau3.3
    ad3antrrr
    @35
    @58
    @36
    simplr
    @60
    @3
    @5
    simprr
    @7
    @4
    cD
    cX
    xmetsym
    syl3anc
    breq1d
    biimpd
    expimpd
    ralimdv
    syl5bir
    expd
    impancom
    mpd
    syl5bi
    syld
    imdistanda
    @36
    @29
    vk
    @12
    r19.26
    @36
    @10
    vk
    @12
    r19.26
    3imtr4g
    @30
    @37
    vk
    @12
    @3
    @5
    @29
    df-3an
    ralbii
    @11
    @39
    vk
    @12
    @3
    @5
    @10
    df-3an
    ralbii
    3imtr4g
    reximdva
    ralimdv
    anim2d
    sylbid
    wph
    @63
    @16
    @0
    wi
    iscau3.3
    @16
    @0
    @63
    @1
    @13
    vj
    cz
    wrex
    #
    vx
    crp
    wral
    #
    wa
    @15
    @65
    @1
    @14
    @64
    vx
    crp
    cZ
    cz
    wss
    @14
    @64
    wi
    cZ
    @50
    cz
    iscau3.2
    cM
    uzssz
    eqsstri
    @13
    vj
    cZ
    cz
    ssrexv
    ax-mp
    ralimi
    anim2i
    vx
    cD
    vj
    vk
    cF
    cX
    iscau2
    syl5ibr
    syl
    impbid
    wph
    @15
    @23
    @1
    wph
    @14
    @22
    vx
    crp
    wph
    @13
    @21
    vj
    cZ
    @35
    @11
    @20
    vk
    @12
    wph
    @34
    @2
    @12
    wcel
    #
    @11
    @20
    wb
    #
    @34
    @66
    wa
    #
    wph
    @34
    @2
    cZ
    wcel
    #
    wa
    #
    @67
    @68
    @34
    @69
    @34
    @66
    simpl
    cM
    @2
    @6
    cZ
    iscau3.2
    uztrn2
    jca
    wph
    @70
    wa
    #
    @5
    @17
    @10
    @19
    @3
    @71
    @4
    cA
    cX
    wph
    @69
    @4
    cA
    wceq
    @34
    iscau4.5
    adantrl
    #
    eleq1d
    @71
    @8
    @18
    @9
    clt
    @71
    @4
    cA
    @7
    cB
    cD
    @72
    wph
    @34
    @7
    cB
    wceq
    @69
    iscau4.6
    adantrr
    oveq12d
    breq1d
    3anbi23d
    sylan2
    anassrs
    ralbidva
    rexbidva
    ralbidv
    anbi2d
    bitrd
end

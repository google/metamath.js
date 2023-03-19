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
include "cz.mm"
include "wrex.mm"
include "crp.mm"
include "wa.mm"
include "cxmt.mm"
include "wb.mm"
include "iscau2.mm"
include "syl.mm"
include "cid.mm"
include "adantr.mm"
include "ssid.mm"
include "simpr.mm"
include "eleq1.mm"
include "xmetsym.mm"
include "fveq2d.mm"
include "cr.mm"
include "c2.mm"
include "cdiv.mm"
include "cxad.mm"
include "cxr.mm"
include "wi.mm"
include "simp1.mm"
include "simp2l.mm"
include "simp3l.mm"
include "xmetcl.mm"
include "syl3anc.mm"
include "simp2r.mm"
include "simp3r.mm"
include "rehalfcld.mm"
include "rexrd.mm"
include "xlt2add.mm"
include "syl22anc.mm"
include "caddc.mm"
include "wceq.mm"
include "rexadd.mm"
include "syl2anc.mm"
include "recnd.mm"
include "2halvesd.mm"
include "eqtrd.mm"
include "breq2d.mm"
include "cle.mm"
include "xmettri.mm"
include "syl13anc.mm"
include "xaddcld.mm"
include "xrlelttr.mm"
include "mpand.mm"
include "sylbid.mm"
include "syld.mm"
include "cvv.mm"
include "ovex.mm"
include "fvi.mm"
include "ax-mp.mm"
include "breq1i.mm"
include "anbi12i.mm"
include "3imtr4g.mm"
include "cau3lem.mm"
include "anbi2i.mm"
include "df-3an.mm"
include "bitr4i.mm"
include "ralbii.mm"
include "rexbii.mm"
include "3bitr3g.mm"
include "rexuz3.mm"
include "ralbidv.mm"
include "bitr4d.mm"
include "pm5.32da.mm"
include "bitrd.mm"

theorem iscau3
  let wph: wff ph
  let vx: setvar x
  let cD: class D
  let vj: setvar j
  let vk: setvar k
  let vm: setvar m
  let cF: class F
  let cM: class M
  let cX: class X
  let cZ: class Z
  let vd: setvar d
  let vf: setvar f
  assume iscau3.2: |- Z = ( ZZ>= ` M )
  assume iscau3.3: |- ( ph -> D e. ( *Met ` X ) )
  assume iscau3.4: |- ( ph -> M e. ZZ )

  disjoint j k
  disjoint j m
  disjoint j x
  disjoint D j
  disjoint k m
  disjoint k x
  disjoint D k
  disjoint m x
  disjoint D m
  disjoint D x
  disjoint F j
  disjoint F k
  disjoint F m
  disjoint F x
  disjoint j ph
  disjoint k ph
  disjoint ph x
  disjoint X j
  disjoint X k
  disjoint X m
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
  disjoint F f
  disjoint X d
  disjoint X f
  assert |- ( ph -> ( F e. ( Cau ` D ) <-> ( F e. ( X ^pm CC ) /\ A. x e. RR+ E. j e. Z A. k e. ( ZZ>= ` j ) ( k e. dom F /\ ( F ` k ) e. X /\ A. m e. ( ZZ>= ` k ) ( ( F ` k ) D ( F ` m ) ) < x ) ) ) )

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
    cz
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
    @5
    @4
    vm
    cv
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
    wph
    cD
    cX
    cxmt
    cfv
    wcel
    #
    @0
    @16
    wb
    iscau3.3
    vx
    cD
    vj
    vk
    cF
    cX
    iscau2
    syl
    wph
    @1
    @15
    @25
    wph
    @1
    wa
    #
    @15
    @23
    vj
    cz
    wrex
    #
    vx
    crp
    wral
    #
    @25
    @27
    @3
    @5
    wa
    #
    @8
    cid
    cfv
    #
    @9
    clt
    wbr
    #
    wa
    #
    vk
    @12
    wral
    #
    vj
    cz
    wrex
    #
    vx
    crp
    wral
    #
    @30
    @18
    cid
    cfv
    #
    @9
    clt
    wbr
    #
    vm
    @20
    wral
    #
    wa
    #
    vk
    @12
    wral
    #
    vj
    cz
    wrex
    #
    vx
    crp
    wral
    #
    @15
    @29
    @27
    @26
    @36
    @43
    wb
    wph
    @26
    @1
    iscau3.3
    adantr
    @26
    @5
    @7
    cX
    wcel
    #
    @17
    cX
    wcel
    #
    @30
    vx
    cD
    vj
    vk
    vm
    cF
    cid
    cz
    cz
    ssid
    @3
    @5
    simpr
    @4
    @7
    cX
    eleq1
    @4
    @17
    cX
    eleq1
    @26
    @44
    @5
    w3a
    @7
    @4
    cD
    co
    @8
    cid
    @7
    @4
    cD
    cX
    xmetsym
    fveq2d
    @26
    @45
    @44
    w3a
    @17
    @7
    cD
    co
    @7
    @17
    cD
    co
    #
    cid
    @17
    @7
    cD
    cX
    xmetsym
    fveq2d
    @26
    @5
    @45
    wa
    #
    @44
    @9
    cr
    wcel
    #
    wa
    #
    w3a
    #
    @8
    @9
    c2
    cdiv
    co
    #
    clt
    wbr
    #
    @46
    @51
    clt
    wbr
    #
    wa
    #
    @19
    @31
    @51
    clt
    wbr
    #
    @46
    cid
    cfv
    #
    @51
    clt
    wbr
    #
    wa
    @38
    @50
    @54
    @8
    @46
    cxad
    co
    #
    @51
    @51
    cxad
    co
    #
    clt
    wbr
    #
    @19
    @50
    @8
    cxr
    wcel
    #
    @46
    cxr
    wcel
    #
    @51
    cxr
    wcel
    #
    @63
    @54
    @60
    wi
    @50
    @26
    @5
    @44
    @61
    @26
    @47
    @49
    simp1
    #
    @26
    @5
    @45
    @49
    simp2l
    #
    @26
    @47
    @44
    @48
    simp3l
    #
    @4
    @7
    cD
    cX
    xmetcl
    syl3anc
    #
    @50
    @26
    @44
    @45
    @62
    @64
    @66
    @26
    @5
    @45
    @49
    simp2r
    #
    @7
    @17
    cD
    cX
    xmetcl
    syl3anc
    #
    @50
    @51
    @50
    @9
    @26
    @47
    @44
    @48
    simp3r
    #
    rehalfcld
    #
    rexrd
    #
    @72
    @8
    @46
    @51
    @51
    xlt2add
    syl22anc
    @50
    @60
    @58
    @9
    clt
    wbr
    #
    @19
    @50
    @59
    @9
    @58
    clt
    @50
    @59
    @51
    @51
    caddc
    co
    #
    @9
    @50
    @51
    cr
    wcel
    #
    @75
    @59
    @74
    wceq
    @71
    @71
    @51
    @51
    rexadd
    syl2anc
    @50
    @9
    @50
    @9
    @70
    recnd
    2halvesd
    eqtrd
    breq2d
    @50
    @18
    @58
    cle
    wbr
    #
    @73
    @19
    @50
    @26
    @5
    @45
    @44
    @76
    @64
    @65
    @68
    @66
    @4
    @17
    @7
    cD
    cX
    xmettri
    syl13anc
    @50
    @18
    cxr
    wcel
    #
    @58
    cxr
    wcel
    @9
    cxr
    wcel
    @76
    @73
    wa
    @19
    wi
    @50
    @26
    @5
    @45
    @77
    @64
    @65
    @68
    @4
    @17
    cD
    cX
    xmetcl
    syl3anc
    @50
    @8
    @46
    @67
    @69
    xaddcld
    @50
    @9
    @70
    rexrd
    @18
    @58
    @9
    xrlelttr
    syl3anc
    mpand
    sylbid
    syld
    @55
    @52
    @57
    @53
    @31
    @8
    @51
    clt
    @8
    cvv
    wcel
    @31
    @8
    wceq
    @4
    @7
    cD
    ovex
    @8
    cvv
    fvi
    ax-mp
    #
    breq1i
    @56
    @46
    @51
    clt
    @46
    cvv
    wcel
    @56
    @46
    wceq
    @7
    @17
    cD
    ovex
    @46
    cvv
    fvi
    ax-mp
    breq1i
    anbi12i
    @37
    @18
    @9
    clt
    @18
    cvv
    wcel
    @37
    @18
    wceq
    @4
    @17
    cD
    ovex
    @18
    cvv
    fvi
    ax-mp
    breq1i
    #
    3imtr4g
    cau3lem
    syl
    @35
    @14
    vx
    crp
    @34
    @13
    vj
    cz
    @33
    @11
    vk
    @12
    @33
    @30
    @10
    wa
    @11
    @32
    @10
    @30
    @31
    @8
    @9
    clt
    @78
    breq1i
    anbi2i
    @3
    @5
    @10
    df-3an
    bitr4i
    ralbii
    rexbii
    ralbii
    @42
    @28
    vx
    crp
    @41
    @23
    vj
    cz
    @40
    @22
    vk
    @12
    @40
    @30
    @21
    wa
    @22
    @39
    @21
    @30
    @38
    @19
    vm
    @20
    @79
    ralbii
    anbi2i
    @3
    @5
    @21
    df-3an
    bitr4i
    ralbii
    rexbii
    ralbii
    3bitr3g
    @27
    @24
    @28
    vx
    crp
    @27
    cM
    cz
    wcel
    #
    @24
    @28
    wb
    wph
    @80
    @1
    iscau3.4
    adantr
    @22
    vj
    vk
    cM
    cZ
    iscau3.2
    rexuz3
    syl
    ralbidv
    bitr4d
    pm5.32da
    bitrd
end

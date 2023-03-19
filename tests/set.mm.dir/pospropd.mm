include "cvv.mm"
include "wcel.mm"
include "cv.mm"
include "cple.mm"
include "cfv.mm"
include "wbr.mm"
include "wa.mm"
include "weq.mm"
include "wi.mm"
include "w3a.mm"
include "cbs.mm"
include "wral.mm"
include "cpo.mm"
include "wb.mm"
include "ralrimivva.mm"
include "simp1.mm"
include "jca.mm"
include "breq1.mm"
include "bibi12d.mm"
include "breq2.mm"
include "rspc2va.mm"
include "sylan.mm"
include "3adantl3.mm"
include "3simpb.mm"
include "3comr.mm"
include "anbi12d.mm"
include "imbi1d.mm"
include "3adantl1.mm"
include "imbi12d.mm"
include "3anbi123d.mm"
include "sylan2.mm"
include "ancoms.mm"
include "3exp2.mm"
include "imp42.mm"
include "ralbidva.mm"
include "2ralbidva.mm"
include "wceq.mm"
include "raleq.mm"
include "raleqbi1dv.mm"
include "syl.mm"
include "3bitr3d.mm"
include "elexd.mm"
include "biantrurd.mm"
include "eqid.mm"
include "ispos.mm"
include "3bitr4g.mm"

theorem pospropd
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cB: class B
  let cK: class K
  let cL: class L
  let cV: class V
  let cW: class W
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  assume pospropd.kv: |- ( ph -> K e. V )
  assume pospropd.lv: |- ( ph -> L e. W )
  assume pospropd.kb: |- ( ph -> B = ( Base ` K ) )
  assume pospropd.lb: |- ( ph -> B = ( Base ` L ) )
  assume pospropd.xy: |- ( ( ph /\ ( x e. B /\ y e. B ) ) -> ( x ( le ` K ) y <-> x ( le ` L ) y ) )

  disjoint B x
  disjoint B y
  disjoint x y
  disjoint ph x
  disjoint ph y
  disjoint K x
  disjoint K y
  disjoint L x
  disjoint L y
  disjoint B a
  disjoint B b
  disjoint B c
  disjoint a x
  disjoint b x
  disjoint c x
  disjoint a y
  disjoint b y
  disjoint c y
  disjoint a b
  disjoint a c
  disjoint b c
  disjoint a ph
  disjoint b ph
  disjoint c ph
  disjoint K a
  disjoint K b
  disjoint K c
  disjoint L a
  disjoint L b
  disjoint L c
  assert |- ( ph -> ( K e. Poset <-> L e. Poset ) )

  proof
    wph
    cK
    cvv
    wcel
    #
    va
    cv
    #
    @1
    cK
    cple
    cfv
    #
    wbr
    #
    @1
    vb
    cv
    #
    @2
    wbr
    #
    @4
    @1
    @2
    wbr
    #
    wa
    #
    va
    vb
    weq
    #
    wi
    #
    @5
    @4
    vc
    cv
    #
    @2
    wbr
    #
    wa
    #
    @1
    @10
    @2
    wbr
    #
    wi
    #
    w3a
    #
    vc
    cK
    cbs
    cfv
    #
    wral
    #
    vb
    @16
    wral
    #
    va
    @16
    wral
    #
    wa
    #
    cL
    cvv
    wcel
    #
    @1
    @1
    cL
    cple
    cfv
    #
    wbr
    #
    @1
    @4
    @22
    wbr
    #
    @4
    @1
    @22
    wbr
    #
    wa
    #
    @8
    wi
    #
    @24
    @4
    @10
    @22
    wbr
    #
    wa
    #
    @1
    @10
    @22
    wbr
    #
    wi
    #
    w3a
    #
    vc
    cL
    cbs
    cfv
    #
    wral
    #
    vb
    @33
    wral
    #
    va
    @33
    wral
    #
    wa
    #
    cK
    cpo
    wcel
    cL
    cpo
    wcel
    wph
    @19
    @36
    @20
    @37
    wph
    @15
    vc
    cB
    wral
    #
    vb
    cB
    wral
    #
    va
    cB
    wral
    #
    @32
    vc
    cB
    wral
    #
    vb
    cB
    wral
    #
    va
    cB
    wral
    #
    @19
    @36
    wph
    @38
    @41
    va
    vb
    cB
    cB
    wph
    @1
    cB
    wcel
    #
    @4
    cB
    wcel
    #
    wa
    wa
    @15
    @32
    vc
    cB
    wph
    @44
    @45
    @10
    cB
    wcel
    #
    @15
    @32
    wb
    #
    wph
    @44
    @45
    @46
    @47
    @44
    @45
    @46
    w3a
    #
    wph
    @47
    wph
    @48
    vx
    cv
    #
    vy
    cv
    #
    @2
    wbr
    #
    @49
    @50
    @22
    wbr
    #
    wb
    #
    vy
    cB
    wral
    vx
    cB
    wral
    #
    @47
    wph
    @53
    vx
    vy
    cB
    cB
    pospropd.xy
    ralrimivva
    @48
    @54
    wa
    #
    @3
    @23
    @9
    @27
    @14
    @31
    @48
    @44
    @44
    wa
    @54
    @3
    @23
    wb
    #
    @48
    @44
    @44
    @44
    @45
    @46
    simp1
    #
    @57
    jca
    @53
    @56
    @1
    @50
    @2
    wbr
    #
    @1
    @50
    @22
    wbr
    #
    wb
    #
    vx
    vy
    @1
    @1
    cB
    cB
    vx
    va
    weq
    @51
    @58
    @52
    @59
    @49
    @1
    @50
    @2
    breq1
    @49
    @1
    @50
    @22
    breq1
    bibi12d
    #
    vy
    va
    weq
    #
    @58
    @3
    @59
    @23
    @50
    @1
    @1
    @2
    breq2
    @50
    @1
    @1
    @22
    breq2
    bibi12d
    rspc2va
    sylan
    @55
    @7
    @26
    @8
    @55
    @5
    @24
    @6
    @25
    @44
    @45
    @54
    @5
    @24
    wb
    #
    @46
    @53
    @63
    @60
    vx
    vy
    @1
    @4
    cB
    cB
    @61
    vy
    vb
    weq
    @58
    @5
    @59
    @24
    @50
    @4
    @1
    @2
    breq2
    @50
    @4
    @1
    @22
    breq2
    bibi12d
    rspc2va
    3adantl3
    #
    @48
    @45
    @44
    wa
    #
    @54
    @6
    @25
    wb
    #
    @45
    @46
    @44
    @65
    @45
    @46
    @44
    3simpb
    3comr
    @53
    @66
    @4
    @50
    @2
    wbr
    #
    @4
    @50
    @22
    wbr
    #
    wb
    #
    vx
    vy
    @4
    @1
    cB
    cB
    vx
    vb
    weq
    @51
    @67
    @52
    @68
    @49
    @4
    @50
    @2
    breq1
    @49
    @4
    @50
    @22
    breq1
    bibi12d
    #
    @62
    @67
    @6
    @68
    @25
    @50
    @1
    @4
    @2
    breq2
    @50
    @1
    @4
    @22
    breq2
    bibi12d
    rspc2va
    sylan
    anbi12d
    imbi1d
    @55
    @12
    @29
    @13
    @30
    @55
    @5
    @24
    @11
    @28
    @64
    @45
    @46
    @54
    @11
    @28
    wb
    #
    @44
    @53
    @71
    @69
    vx
    vy
    @4
    @10
    cB
    cB
    @70
    vy
    vc
    weq
    #
    @67
    @11
    @68
    @28
    @50
    @10
    @4
    @2
    breq2
    @50
    @10
    @4
    @22
    breq2
    bibi12d
    rspc2va
    3adantl1
    anbi12d
    @48
    @44
    @46
    wa
    @54
    @13
    @30
    wb
    #
    @44
    @45
    @46
    3simpb
    @53
    @73
    @60
    vx
    vy
    @1
    @10
    cB
    cB
    @61
    @72
    @58
    @13
    @59
    @30
    @50
    @10
    @1
    @2
    breq2
    @50
    @10
    @1
    @22
    breq2
    bibi12d
    rspc2va
    sylan
    imbi12d
    3anbi123d
    sylan2
    ancoms
    3exp2
    imp42
    ralbidva
    2ralbidva
    wph
    cB
    @16
    wceq
    @40
    @19
    wb
    pospropd.kb
    @39
    @18
    va
    cB
    @16
    @38
    @17
    vb
    cB
    @16
    @15
    vc
    cB
    @16
    raleq
    raleqbi1dv
    raleqbi1dv
    syl
    wph
    cB
    @33
    wceq
    @43
    @36
    wb
    pospropd.lb
    @42
    @35
    va
    cB
    @33
    @41
    @34
    vb
    cB
    @33
    @32
    vc
    cB
    @33
    raleq
    raleqbi1dv
    raleqbi1dv
    syl
    3bitr3d
    wph
    @0
    @19
    wph
    cK
    cV
    pospropd.kv
    elexd
    biantrurd
    wph
    @21
    @36
    wph
    cL
    cW
    pospropd.lv
    elexd
    biantrurd
    3bitr3d
    va
    vb
    vc
    @16
    cK
    @2
    @16
    eqid
    @2
    eqid
    ispos
    va
    vb
    vc
    @33
    cL
    @22
    @33
    eqid
    @22
    eqid
    ispos
    3bitr4g
end

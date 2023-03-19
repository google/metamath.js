include "cmhm.mm"
include "co.mm"
include "cmnd.mm"
include "wcel.mm"
include "wa.mm"
include "cbs.mm"
include "cfv.mm"
include "cv.mm"
include "wf.mm"
include "cplusg.mm"
include "wceq.mm"
include "wral.mm"
include "c0g.mm"
include "w3a.mm"
include "wb.mm"
include "fveq2d.mm"
include "adantlr.mm"
include "ffvelrn.mm"
include "anim12dan.mm"
include "ralrimivva.mm"
include "oveq1.mm"
include "eqeq12d.mm"
include "oveq2.mm"
include "cbvral2v.mm"
include "sylib.mm"
include "rspc2va.mm"
include "syl2anr.mm"
include "anassrs.mm"
include "2ralbidva.mm"
include "adantrl.mm"
include "raleq.mm"
include "raleqbi1dv.mm"
include "syl.mm"
include "adantr.mm"
include "3bitr3d.mm"
include "grpidpropd.mm"
include "anbi12d.mm"
include "pm5.32da.mm"
include "feq23d.mm"
include "anbi1d.mm"
include "3anass.mm"
include "3bitr4g.mm"
include "mndpropd.mm"
include "bitrd.mm"
include "eqid.mm"
include "ismhm.mm"
include "eqrdv.mm"

theorem mhmpropd
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cB: class B
  let cC: class C
  let cJ: class J
  let cK: class K
  let cL: class L
  let cM: class M
  let vw: setvar w
  let vz: setvar z
  let vf: setvar f
  assume mhmpropd.a: |- ( ph -> B = ( Base ` J ) )
  assume mhmpropd.b: |- ( ph -> C = ( Base ` K ) )
  assume mhmpropd.c: |- ( ph -> B = ( Base ` L ) )
  assume mhmpropd.d: |- ( ph -> C = ( Base ` M ) )
  assume mhmpropd.e: |- ( ( ph /\ ( x e. B /\ y e. B ) ) -> ( x ( +g ` J ) y ) = ( x ( +g ` L ) y ) )
  assume mhmpropd.f: |- ( ( ph /\ ( x e. C /\ y e. C ) ) -> ( x ( +g ` K ) y ) = ( x ( +g ` M ) y ) )

  disjoint x y
  disjoint B x
  disjoint B y
  disjoint C x
  disjoint C y
  disjoint J x
  disjoint J y
  disjoint L x
  disjoint L y
  disjoint ph x
  disjoint ph y
  disjoint K x
  disjoint K y
  disjoint M x
  disjoint M y
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint C w
  disjoint x z
  disjoint y z
  disjoint C z
  disjoint f x
  disjoint f y
  disjoint J f
  disjoint L f
  disjoint f ph
  disjoint f w
  disjoint f z
  disjoint K f
  disjoint K w
  disjoint K z
  disjoint M f
  disjoint M w
  disjoint M z
  assert |- ( ph -> ( J MndHom K ) = ( L MndHom M ) )

  proof
    wph
    vf
    cJ
    cK
    cmhm
    co
    #
    cL
    cM
    cmhm
    co
    #
    wph
    cJ
    cmnd
    wcel
    #
    cK
    cmnd
    wcel
    #
    wa
    #
    cJ
    cbs
    cfv
    #
    cK
    cbs
    cfv
    #
    vf
    cv
    #
    wf
    #
    vx
    cv
    #
    vy
    cv
    #
    cJ
    cplusg
    cfv
    #
    co
    #
    @7
    cfv
    #
    @9
    @7
    cfv
    #
    @10
    @7
    cfv
    #
    cK
    cplusg
    cfv
    #
    co
    #
    wceq
    #
    vy
    @5
    wral
    #
    vx
    @5
    wral
    #
    cJ
    c0g
    cfv
    #
    @7
    cfv
    #
    cK
    c0g
    cfv
    #
    wceq
    #
    w3a
    #
    wa
    #
    cL
    cmnd
    wcel
    #
    cM
    cmnd
    wcel
    #
    wa
    #
    cL
    cbs
    cfv
    #
    cM
    cbs
    cfv
    #
    @7
    wf
    #
    @9
    @10
    cL
    cplusg
    cfv
    #
    co
    #
    @7
    cfv
    #
    @14
    @15
    cM
    cplusg
    cfv
    #
    co
    #
    wceq
    #
    vy
    @30
    wral
    #
    vx
    @30
    wral
    #
    cL
    c0g
    cfv
    #
    @7
    cfv
    #
    cM
    c0g
    cfv
    #
    wceq
    #
    w3a
    #
    wa
    #
    @7
    @0
    wcel
    @7
    @1
    wcel
    wph
    @26
    @4
    @45
    wa
    @46
    wph
    @4
    @25
    @45
    wph
    @4
    wa
    #
    @8
    @20
    @24
    wa
    #
    wa
    #
    @32
    @40
    @44
    wa
    #
    wa
    #
    @25
    @45
    @47
    cB
    cC
    @7
    wf
    #
    @48
    wa
    @52
    @50
    wa
    @49
    @51
    @47
    @52
    @48
    @50
    wph
    @4
    @52
    @48
    @50
    wb
    wph
    @4
    @52
    wa
    #
    wa
    #
    @20
    @40
    @24
    @44
    @54
    @18
    vy
    cB
    wral
    #
    vx
    cB
    wral
    #
    @38
    vy
    cB
    wral
    #
    vx
    cB
    wral
    #
    @20
    @40
    wph
    @52
    @56
    @58
    wb
    @4
    wph
    @52
    wa
    #
    @18
    @38
    vx
    vy
    cB
    cB
    @59
    @9
    cB
    wcel
    #
    @10
    cB
    wcel
    #
    wa
    #
    wa
    @13
    @35
    @17
    @37
    wph
    @62
    @13
    @35
    wceq
    @52
    wph
    @62
    wa
    @12
    @34
    @7
    mhmpropd.e
    fveq2d
    adantlr
    wph
    @52
    @62
    @17
    @37
    wceq
    #
    @52
    @62
    wa
    @14
    cC
    wcel
    #
    @15
    cC
    wcel
    #
    wa
    vw
    cv
    #
    vz
    cv
    #
    @16
    co
    #
    @66
    @67
    @36
    co
    #
    wceq
    #
    vz
    cC
    wral
    vw
    cC
    wral
    #
    @63
    wph
    @52
    @60
    @64
    @61
    @65
    cB
    cC
    @9
    @7
    ffvelrn
    cB
    cC
    @10
    @7
    ffvelrn
    anim12dan
    wph
    @9
    @10
    @16
    co
    #
    @9
    @10
    @36
    co
    #
    wceq
    #
    vy
    cC
    wral
    vx
    cC
    wral
    @71
    wph
    @74
    vx
    vy
    cC
    cC
    mhmpropd.f
    ralrimivva
    @74
    @70
    @66
    @10
    @16
    co
    #
    @66
    @10
    @36
    co
    #
    wceq
    vx
    vy
    vw
    vz
    cC
    cC
    @9
    @66
    wceq
    @72
    @75
    @73
    @76
    @9
    @66
    @10
    @16
    oveq1
    @9
    @66
    @10
    @36
    oveq1
    eqeq12d
    @10
    @67
    wceq
    @75
    @68
    @76
    @69
    @10
    @67
    @66
    @16
    oveq2
    @10
    @67
    @66
    @36
    oveq2
    eqeq12d
    cbvral2v
    sylib
    @70
    @63
    @14
    @67
    @16
    co
    #
    @14
    @67
    @36
    co
    #
    wceq
    vw
    vz
    @14
    @15
    cC
    cC
    @66
    @14
    wceq
    @68
    @77
    @69
    @78
    @66
    @14
    @67
    @16
    oveq1
    @66
    @14
    @67
    @36
    oveq1
    eqeq12d
    @67
    @15
    wceq
    @77
    @17
    @78
    @37
    @67
    @15
    @14
    @16
    oveq2
    @67
    @15
    @14
    @36
    oveq2
    eqeq12d
    rspc2va
    syl2anr
    anassrs
    eqeq12d
    2ralbidva
    adantrl
    wph
    @56
    @20
    wb
    #
    @53
    wph
    cB
    @5
    wceq
    #
    @79
    mhmpropd.a
    @55
    @19
    vx
    cB
    @5
    @18
    vy
    cB
    @5
    raleq
    raleqbi1dv
    syl
    adantr
    wph
    @58
    @40
    wb
    #
    @53
    wph
    cB
    @30
    wceq
    #
    @81
    mhmpropd.c
    @57
    @39
    vx
    cB
    @30
    @38
    vy
    cB
    @30
    raleq
    raleqbi1dv
    syl
    adantr
    3bitr3d
    @54
    @22
    @42
    @23
    @43
    @54
    @21
    @41
    @7
    @54
    vx
    vy
    cB
    cJ
    cL
    wph
    @80
    @53
    mhmpropd.a
    adantr
    wph
    @82
    @53
    mhmpropd.c
    adantr
    wph
    @62
    @12
    @34
    wceq
    @53
    mhmpropd.e
    adantlr
    grpidpropd
    fveq2d
    @54
    vx
    vy
    cC
    cK
    cM
    wph
    cC
    @6
    wceq
    @53
    mhmpropd.b
    adantr
    wph
    cC
    @31
    wceq
    @53
    mhmpropd.d
    adantr
    wph
    @9
    cC
    wcel
    @10
    cC
    wcel
    wa
    @74
    @53
    mhmpropd.f
    adantlr
    grpidpropd
    eqeq12d
    anbi12d
    anassrs
    pm5.32da
    @47
    @52
    @8
    @48
    wph
    @52
    @8
    wb
    @4
    wph
    cB
    cC
    @5
    @6
    @7
    mhmpropd.a
    mhmpropd.b
    feq23d
    adantr
    anbi1d
    @47
    @52
    @32
    @50
    wph
    @52
    @32
    wb
    @4
    wph
    cB
    cC
    @30
    @31
    @7
    mhmpropd.c
    mhmpropd.d
    feq23d
    adantr
    anbi1d
    3bitr3d
    @8
    @20
    @24
    3anass
    @32
    @40
    @44
    3anass
    3bitr4g
    pm5.32da
    wph
    @4
    @29
    @45
    wph
    @2
    @27
    @3
    @28
    wph
    vx
    vy
    cB
    cJ
    cL
    mhmpropd.a
    mhmpropd.c
    mhmpropd.e
    mndpropd
    wph
    vx
    vy
    cC
    cK
    cM
    mhmpropd.b
    mhmpropd.d
    mhmpropd.f
    mndpropd
    anbi12d
    anbi1d
    bitrd
    vx
    vy
    @5
    @6
    @11
    @16
    cJ
    cK
    @7
    @23
    @21
    @5
    eqid
    @6
    eqid
    @11
    eqid
    @16
    eqid
    @21
    eqid
    @23
    eqid
    ismhm
    vx
    vy
    @30
    @31
    @33
    @36
    cL
    cM
    @7
    @43
    @41
    @30
    eqid
    @31
    eqid
    @33
    eqid
    @36
    eqid
    @41
    eqid
    @43
    eqid
    ismhm
    3bitr4g
    eqrdv
end

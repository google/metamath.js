include "cmgmhm.mm"
include "co.mm"
include "cmgm.mm"
include "wcel.mm"
include "wa.mm"
include "cbs.mm"
include "cfv.mm"
include "cv.mm"
include "wf.mm"
include "cplusg.mm"
include "wceq.mm"
include "wral.mm"
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
include "pm5.32da.mm"
include "feq23d.mm"
include "anbi1d.mm"
include "mgmpropd.mm"
include "anbi12d.mm"
include "bitrd.mm"
include "eqid.mm"
include "ismgmhm.mm"
include "3bitr4g.mm"
include "eqrdv.mm"

theorem mgmhmpropd
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
  let vk: setvar k
  assume mgmhmpropd.a: |- ( ph -> B = ( Base ` J ) )
  assume mgmhmpropd.b: |- ( ph -> C = ( Base ` K ) )
  assume mgmhmpropd.c: |- ( ph -> B = ( Base ` L ) )
  assume mgmhmpropd.d: |- ( ph -> C = ( Base ` M ) )
  assume mgmhmpropd.0: |- ( ph -> B =/= (/) )
  assume mgmhmpropd.C: |- ( ph -> C =/= (/) )
  assume mgmhmpropd.e: |- ( ( ph /\ ( x e. B /\ y e. B ) ) -> ( x ( +g ` J ) y ) = ( x ( +g ` L ) y ) )
  assume mgmhmpropd.f: |- ( ( ph /\ ( x e. C /\ y e. C ) ) -> ( x ( +g ` K ) y ) = ( x ( +g ` M ) y ) )

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
  disjoint k x
  assert |- ( ph -> ( J MgmHom K ) = ( L MgmHom M ) )

  proof
    wph
    vf
    cJ
    cK
    cmgmhm
    co
    #
    cL
    cM
    cmgmhm
    co
    #
    wph
    cJ
    cmgm
    wcel
    #
    cK
    cmgm
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
    wa
    #
    wa
    #
    cL
    cmgm
    wcel
    #
    cM
    cmgm
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
    @26
    wral
    #
    vx
    @26
    wral
    #
    wa
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
    @22
    @4
    @37
    wa
    @38
    wph
    @4
    @21
    @37
    wph
    @4
    wa
    #
    cB
    cC
    @7
    wf
    #
    @20
    wa
    @40
    @36
    wa
    @21
    @37
    @39
    @40
    @20
    @36
    wph
    @4
    @40
    @20
    @36
    wb
    wph
    @4
    @40
    wa
    #
    wa
    @18
    vy
    cB
    wral
    #
    vx
    cB
    wral
    #
    @34
    vy
    cB
    wral
    #
    vx
    cB
    wral
    #
    @20
    @36
    wph
    @40
    @43
    @45
    wb
    @4
    wph
    @40
    wa
    #
    @18
    @34
    vx
    vy
    cB
    cB
    @46
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
    @31
    @17
    @33
    wph
    @49
    @13
    @31
    wceq
    @40
    wph
    @49
    wa
    @12
    @30
    @7
    mgmhmpropd.e
    fveq2d
    adantlr
    wph
    @40
    @49
    @17
    @33
    wceq
    #
    @40
    @49
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
    @53
    @54
    @32
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
    @50
    wph
    @40
    @47
    @51
    @48
    @52
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
    @32
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
    @58
    wph
    @61
    vx
    vy
    cC
    cC
    mgmhmpropd.f
    ralrimivva
    @61
    @57
    @53
    @10
    @16
    co
    #
    @53
    @10
    @32
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
    @53
    wceq
    @59
    @62
    @60
    @63
    @9
    @53
    @10
    @16
    oveq1
    @9
    @53
    @10
    @32
    oveq1
    eqeq12d
    @10
    @54
    wceq
    @62
    @55
    @63
    @56
    @10
    @54
    @53
    @16
    oveq2
    @10
    @54
    @53
    @32
    oveq2
    eqeq12d
    cbvral2v
    sylib
    @57
    @50
    @14
    @54
    @16
    co
    #
    @14
    @54
    @32
    co
    #
    wceq
    vw
    vz
    @14
    @15
    cC
    cC
    @53
    @14
    wceq
    @55
    @64
    @56
    @65
    @53
    @14
    @54
    @16
    oveq1
    @53
    @14
    @54
    @32
    oveq1
    eqeq12d
    @54
    @15
    wceq
    @64
    @17
    @65
    @33
    @54
    @15
    @14
    @16
    oveq2
    @54
    @15
    @14
    @32
    oveq2
    eqeq12d
    rspc2va
    syl2anr
    anassrs
    eqeq12d
    2ralbidva
    adantrl
    wph
    @43
    @20
    wb
    #
    @41
    wph
    cB
    @5
    wceq
    @66
    mgmhmpropd.a
    @42
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
    @45
    @36
    wb
    #
    @41
    wph
    cB
    @26
    wceq
    @67
    mgmhmpropd.c
    @44
    @35
    vx
    cB
    @26
    @34
    vy
    cB
    @26
    raleq
    raleqbi1dv
    syl
    adantr
    3bitr3d
    anassrs
    pm5.32da
    @39
    @40
    @8
    @20
    wph
    @40
    @8
    wb
    @4
    wph
    cB
    cC
    @5
    @6
    @7
    mgmhmpropd.a
    mgmhmpropd.b
    feq23d
    adantr
    anbi1d
    @39
    @40
    @28
    @36
    wph
    @40
    @28
    wb
    @4
    wph
    cB
    cC
    @26
    @27
    @7
    mgmhmpropd.c
    mgmhmpropd.d
    feq23d
    adantr
    anbi1d
    3bitr3d
    pm5.32da
    wph
    @4
    @25
    @37
    wph
    @2
    @23
    @3
    @24
    wph
    vx
    vy
    cB
    cJ
    cL
    mgmhmpropd.a
    mgmhmpropd.c
    mgmhmpropd.0
    mgmhmpropd.e
    mgmpropd
    wph
    vx
    vy
    cC
    cK
    cM
    mgmhmpropd.b
    mgmhmpropd.d
    mgmhmpropd.C
    mgmhmpropd.f
    mgmpropd
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
    @5
    eqid
    @6
    eqid
    @11
    eqid
    @16
    eqid
    ismgmhm
    vx
    vy
    @26
    @27
    @29
    @32
    cL
    cM
    @7
    @26
    eqid
    @27
    eqid
    @29
    eqid
    @32
    eqid
    ismgmhm
    3bitr4g
    eqrdv
end

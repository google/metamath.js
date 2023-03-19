include "cabv.mm"
include "cfv.mm"
include "crg.mm"
include "wcel.mm"
include "cbs.mm"
include "cc0.mm"
include "cpnf.mm"
include "cico.mm"
include "co.mm"
include "cv.mm"
include "wf.mm"
include "wceq.mm"
include "c0g.mm"
include "wb.mm"
include "cmulr.mm"
include "cmul.mm"
include "cplusg.mm"
include "caddc.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "wral.mm"
include "ringpropd.mm"
include "eqtr3d.mm"
include "feq2d.mm"
include "grpidpropd.mm"
include "adantr.mm"
include "eqeq2d.mm"
include "bibi2d.mm"
include "fveq2d.mm"
include "eqeq1d.mm"
include "breq1d.mm"
include "anbi12d.mm"
include "anassrs.mm"
include "ralbidva.mm"
include "raleqdv.mm"
include "anbi2d.mm"
include "raleqbidv.mm"
include "3bitr3d.mm"
include "eqid.mm"
include "abvrcl.mm"
include "isabv.mm"
include "biadan2.mm"
include "3bitr4g.mm"
include "eqrdv.mm"

theorem abvpropd
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cB: class B
  let cK: class K
  let cL: class L
  let vf: setvar f
  assume abvpropd.1: |- ( ph -> B = ( Base ` K ) )
  assume abvpropd.2: |- ( ph -> B = ( Base ` L ) )
  assume abvpropd.3: |- ( ( ph /\ ( x e. B /\ y e. B ) ) -> ( x ( +g ` K ) y ) = ( x ( +g ` L ) y ) )
  assume abvpropd.4: |- ( ( ph /\ ( x e. B /\ y e. B ) ) -> ( x ( .r ` K ) y ) = ( x ( .r ` L ) y ) )

  disjoint x y
  disjoint B x
  disjoint B y
  disjoint K x
  disjoint K y
  disjoint L x
  disjoint L y
  disjoint ph x
  disjoint ph y
  disjoint f x
  disjoint f y
  disjoint K f
  disjoint L f
  disjoint f ph
  assert |- ( ph -> ( AbsVal ` K ) = ( AbsVal ` L ) )

  proof
    wph
    vf
    cK
    cabv
    cfv
    #
    cL
    cabv
    cfv
    #
    wph
    cK
    crg
    wcel
    #
    cK
    cbs
    cfv
    #
    cc0
    cpnf
    cico
    co
    #
    vf
    cv
    #
    wf
    #
    vx
    cv
    #
    @5
    cfv
    #
    cc0
    wceq
    #
    @7
    cK
    c0g
    cfv
    #
    wceq
    #
    wb
    #
    @7
    vy
    cv
    #
    cK
    cmulr
    cfv
    #
    co
    #
    @5
    cfv
    #
    @8
    @13
    @5
    cfv
    #
    cmul
    co
    #
    wceq
    #
    @7
    @13
    cK
    cplusg
    cfv
    #
    co
    #
    @5
    cfv
    #
    @8
    @17
    caddc
    co
    #
    cle
    wbr
    #
    wa
    #
    vy
    @3
    wral
    #
    wa
    #
    vx
    @3
    wral
    #
    wa
    #
    wa
    cL
    crg
    wcel
    #
    cL
    cbs
    cfv
    #
    @4
    @5
    wf
    #
    @9
    @7
    cL
    c0g
    cfv
    #
    wceq
    #
    wb
    #
    @7
    @13
    cL
    cmulr
    cfv
    #
    co
    #
    @5
    cfv
    #
    @18
    wceq
    #
    @7
    @13
    cL
    cplusg
    cfv
    #
    co
    #
    @5
    cfv
    #
    @23
    cle
    wbr
    #
    wa
    #
    vy
    @31
    wral
    #
    wa
    #
    vx
    @31
    wral
    #
    wa
    #
    wa
    @5
    @0
    wcel
    #
    @5
    @1
    wcel
    #
    wph
    @2
    @30
    @29
    @48
    wph
    vx
    vy
    cB
    cK
    cL
    abvpropd.1
    abvpropd.2
    abvpropd.3
    abvpropd.4
    ringpropd
    wph
    @6
    @32
    @28
    @47
    wph
    @3
    @31
    @4
    @5
    wph
    cB
    @3
    @31
    abvpropd.1
    abvpropd.2
    eqtr3d
    feq2d
    wph
    @12
    @25
    vy
    cB
    wral
    #
    wa
    #
    vx
    cB
    wral
    @35
    @44
    vy
    cB
    wral
    #
    wa
    #
    vx
    cB
    wral
    @28
    @47
    wph
    @52
    @54
    vx
    cB
    wph
    @7
    cB
    wcel
    #
    wa
    #
    @12
    @35
    @51
    @53
    @56
    @11
    @34
    @9
    @56
    @10
    @33
    @7
    wph
    @10
    @33
    wceq
    @55
    wph
    vx
    vy
    cB
    cK
    cL
    abvpropd.1
    abvpropd.2
    abvpropd.3
    grpidpropd
    adantr
    eqeq2d
    bibi2d
    @56
    @25
    @44
    vy
    cB
    wph
    @55
    @13
    cB
    wcel
    #
    @25
    @44
    wb
    wph
    @55
    @57
    wa
    wa
    #
    @19
    @39
    @24
    @43
    @58
    @16
    @38
    @18
    @58
    @15
    @37
    @5
    abvpropd.4
    fveq2d
    eqeq1d
    @58
    @22
    @42
    @23
    cle
    @58
    @21
    @41
    @5
    abvpropd.3
    fveq2d
    breq1d
    anbi12d
    anassrs
    ralbidva
    anbi12d
    ralbidva
    wph
    @52
    @27
    vx
    cB
    @3
    abvpropd.1
    wph
    @51
    @26
    @12
    wph
    @25
    vy
    cB
    @3
    abvpropd.1
    raleqdv
    anbi2d
    raleqbidv
    wph
    @54
    @46
    vx
    cB
    @31
    abvpropd.2
    wph
    @53
    @45
    @35
    wph
    @44
    vy
    cB
    @31
    abvpropd.2
    raleqdv
    anbi2d
    raleqbidv
    3bitr3d
    anbi12d
    anbi12d
    @49
    @2
    @29
    @0
    cK
    @5
    @0
    eqid
    #
    abvrcl
    vx
    vy
    @0
    @3
    @20
    cK
    @14
    @5
    @10
    @59
    @3
    eqid
    @20
    eqid
    @14
    eqid
    @10
    eqid
    isabv
    biadan2
    @50
    @30
    @48
    @1
    cL
    @5
    @1
    eqid
    #
    abvrcl
    vx
    vy
    @1
    @31
    @40
    cL
    @36
    @5
    @33
    @60
    @31
    eqid
    @40
    eqid
    @36
    eqid
    @33
    eqid
    isabv
    biadan2
    3bitr4g
    eqrdv
end

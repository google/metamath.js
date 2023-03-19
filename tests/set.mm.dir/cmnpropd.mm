include "cmnd.mm"
include "wcel.mm"
include "cv.mm"
include "cplusg.mm"
include "cfv.mm"
include "co.mm"
include "wceq.mm"
include "cbs.mm"
include "wral.mm"
include "wa.mm"
include "ccmn.mm"
include "mndpropd.mm"
include "oveqrspc2v.mm"
include "ancom2s.mm"
include "eqeq12d.mm"
include "2ralbidva.mm"
include "raleqdv.mm"
include "raleqbidv.mm"
include "3bitr3d.mm"
include "anbi12d.mm"
include "eqid.mm"
include "iscmn.mm"
include "3bitr4g.mm"

theorem cmnpropd
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cB: class B
  let cK: class K
  let cL: class L
  let vu: setvar u
  let vv: setvar v
  assume ablpropd.1: |- ( ph -> B = ( Base ` K ) )
  assume ablpropd.2: |- ( ph -> B = ( Base ` L ) )
  assume ablpropd.3: |- ( ( ph /\ ( x e. B /\ y e. B ) ) -> ( x ( +g ` K ) y ) = ( x ( +g ` L ) y ) )

  disjoint x y
  disjoint B x
  disjoint B y
  disjoint K x
  disjoint K y
  disjoint L x
  disjoint L y
  disjoint ph x
  disjoint ph y
  disjoint u v
  disjoint u x
  disjoint u y
  disjoint B u
  disjoint v x
  disjoint v y
  disjoint B v
  disjoint K u
  disjoint K v
  disjoint L u
  disjoint L v
  disjoint ph u
  disjoint ph v
  assert |- ( ph -> ( K e. CMnd <-> L e. CMnd ) )

  proof
    wph
    cK
    cmnd
    wcel
    #
    vu
    cv
    #
    vv
    cv
    #
    cK
    cplusg
    cfv
    #
    co
    #
    @2
    @1
    @3
    co
    #
    wceq
    #
    vv
    cK
    cbs
    cfv
    #
    wral
    #
    vu
    @7
    wral
    #
    wa
    cL
    cmnd
    wcel
    #
    @1
    @2
    cL
    cplusg
    cfv
    #
    co
    #
    @2
    @1
    @11
    co
    #
    wceq
    #
    vv
    cL
    cbs
    cfv
    #
    wral
    #
    vu
    @15
    wral
    #
    wa
    cK
    ccmn
    wcel
    cL
    ccmn
    wcel
    wph
    @0
    @10
    @9
    @17
    wph
    vx
    vy
    cB
    cK
    cL
    ablpropd.1
    ablpropd.2
    ablpropd.3
    mndpropd
    wph
    @6
    vv
    cB
    wral
    #
    vu
    cB
    wral
    @14
    vv
    cB
    wral
    #
    vu
    cB
    wral
    @9
    @17
    wph
    @6
    @14
    vu
    vv
    cB
    cB
    wph
    @1
    cB
    wcel
    #
    @2
    cB
    wcel
    #
    wa
    wa
    @4
    @12
    @5
    @13
    wph
    vx
    vy
    cB
    cB
    @3
    @11
    @1
    @2
    ablpropd.3
    oveqrspc2v
    wph
    @21
    @20
    @5
    @13
    wceq
    wph
    vx
    vy
    cB
    cB
    @3
    @11
    @2
    @1
    ablpropd.3
    oveqrspc2v
    ancom2s
    eqeq12d
    2ralbidva
    wph
    @18
    @8
    vu
    cB
    @7
    ablpropd.1
    wph
    @6
    vv
    cB
    @7
    ablpropd.1
    raleqdv
    raleqbidv
    wph
    @19
    @16
    vu
    cB
    @15
    ablpropd.2
    wph
    @14
    vv
    cB
    @15
    ablpropd.2
    raleqdv
    raleqbidv
    3bitr3d
    anbi12d
    vu
    vv
    @7
    @3
    cK
    @7
    eqid
    @3
    eqid
    iscmn
    vu
    vv
    @15
    @11
    cL
    @15
    eqid
    @11
    eqid
    iscmn
    3bitr4g
end

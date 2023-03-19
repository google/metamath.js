include "crg.mm"
include "wcel.mm"
include "cmgp.mm"
include "cfv.mm"
include "ccmn.mm"
include "wa.mm"
include "ccrg.mm"
include "ringpropd.mm"
include "cbs.mm"
include "eqid.mm"
include "mgpbas.mm"
include "syl6eq.mm"
include "cv.mm"
include "cmulr.mm"
include "co.mm"
include "cplusg.mm"
include "mgpplusg.mm"
include "oveqi.mm"
include "3eqtr3g.mm"
include "cmnpropd.mm"
include "anbi12d.mm"
include "iscrng.mm"
include "3bitr4g.mm"

theorem crngpropd
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cB: class B
  let cK: class K
  let cL: class L
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  assume ringpropd.1: |- ( ph -> B = ( Base ` K ) )
  assume ringpropd.2: |- ( ph -> B = ( Base ` L ) )
  assume ringpropd.3: |- ( ( ph /\ ( x e. B /\ y e. B ) ) -> ( x ( +g ` K ) y ) = ( x ( +g ` L ) y ) )
  assume ringpropd.4: |- ( ( ph /\ ( x e. B /\ y e. B ) ) -> ( x ( .r ` K ) y ) = ( x ( .r ` L ) y ) )

  disjoint x y
  disjoint B x
  disjoint B y
  disjoint K x
  disjoint K y
  disjoint ph x
  disjoint ph y
  disjoint L x
  disjoint L y
  disjoint u v
  disjoint u w
  disjoint u x
  disjoint u y
  disjoint B u
  disjoint v w
  disjoint v x
  disjoint v y
  disjoint B v
  disjoint w x
  disjoint w y
  disjoint B w
  disjoint K u
  disjoint K v
  disjoint K w
  disjoint ph u
  disjoint ph v
  disjoint ph w
  disjoint L u
  disjoint L v
  disjoint L w
  assert |- ( ph -> ( K e. CRing <-> L e. CRing ) )

  proof
    wph
    cK
    crg
    wcel
    #
    cK
    cmgp
    cfv
    #
    ccmn
    wcel
    #
    wa
    cL
    crg
    wcel
    #
    cL
    cmgp
    cfv
    #
    ccmn
    wcel
    #
    wa
    cK
    ccrg
    wcel
    cL
    ccrg
    wcel
    wph
    @0
    @3
    @2
    @5
    wph
    vx
    vy
    cB
    cK
    cL
    ringpropd.1
    ringpropd.2
    ringpropd.3
    ringpropd.4
    ringpropd
    wph
    vx
    vy
    cB
    @1
    @4
    wph
    cB
    cK
    cbs
    cfv
    #
    @1
    cbs
    cfv
    ringpropd.1
    @6
    cK
    @1
    @1
    eqid
    #
    @6
    eqid
    mgpbas
    syl6eq
    wph
    cB
    cL
    cbs
    cfv
    #
    @4
    cbs
    cfv
    ringpropd.2
    @8
    cL
    @4
    @4
    eqid
    #
    @8
    eqid
    mgpbas
    syl6eq
    wph
    vx
    cv
    #
    cB
    wcel
    vy
    cv
    #
    cB
    wcel
    wa
    wa
    @10
    @11
    cK
    cmulr
    cfv
    #
    co
    @10
    @11
    cL
    cmulr
    cfv
    #
    co
    @10
    @11
    @1
    cplusg
    cfv
    #
    co
    @10
    @11
    @4
    cplusg
    cfv
    #
    co
    ringpropd.4
    @12
    @14
    @10
    @11
    cK
    @12
    @1
    @7
    @12
    eqid
    mgpplusg
    oveqi
    @13
    @15
    @10
    @11
    cL
    @13
    @4
    @9
    @13
    eqid
    mgpplusg
    oveqi
    3eqtr3g
    cmnpropd
    anbi12d
    cK
    @1
    @7
    iscrng
    cL
    @4
    @9
    iscrng
    3bitr4g
end

include "cmgp.mm"
include "cfv.mm"
include "c0g.mm"
include "cur.mm"
include "cbs.mm"
include "eqid.mm"
include "mgpbas.mm"
include "syl6eq.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "cmulr.mm"
include "co.mm"
include "cplusg.mm"
include "mgpplusg.mm"
include "oveqi.mm"
include "3eqtr3g.mm"
include "grpidpropd.mm"
include "ringidval.mm"
include "3eqtr4g.mm"

theorem rngidpropd
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cB: class B
  let cK: class K
  let cL: class L
  let vz: setvar z
  assume rngidpropd.1: |- ( ph -> B = ( Base ` K ) )
  assume rngidpropd.2: |- ( ph -> B = ( Base ` L ) )
  assume rngidpropd.3: |- ( ( ph /\ ( x e. B /\ y e. B ) ) -> ( x ( .r ` K ) y ) = ( x ( .r ` L ) y ) )

  disjoint x y
  disjoint B x
  disjoint B y
  disjoint K x
  disjoint K y
  disjoint L x
  disjoint L y
  disjoint ph x
  disjoint ph y
  disjoint x z
  disjoint y z
  disjoint K z
  disjoint L z
  disjoint ph z
  assert |- ( ph -> ( 1r ` K ) = ( 1r ` L ) )

  proof
    wph
    cK
    cmgp
    cfv
    #
    c0g
    cfv
    cL
    cmgp
    cfv
    #
    c0g
    cfv
    cK
    cur
    cfv
    #
    cL
    cur
    cfv
    #
    wph
    vx
    vy
    cB
    @0
    @1
    wph
    cB
    cK
    cbs
    cfv
    #
    @0
    cbs
    cfv
    rngidpropd.1
    @4
    cK
    @0
    @0
    eqid
    #
    @4
    eqid
    mgpbas
    syl6eq
    wph
    cB
    cL
    cbs
    cfv
    #
    @1
    cbs
    cfv
    rngidpropd.2
    @6
    cL
    @1
    @1
    eqid
    #
    @6
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
    @8
    @9
    cK
    cmulr
    cfv
    #
    co
    @8
    @9
    cL
    cmulr
    cfv
    #
    co
    @8
    @9
    @0
    cplusg
    cfv
    #
    co
    @8
    @9
    @1
    cplusg
    cfv
    #
    co
    rngidpropd.3
    @10
    @12
    @8
    @9
    cK
    @10
    @0
    @5
    @10
    eqid
    mgpplusg
    oveqi
    @11
    @13
    @8
    @9
    cL
    @11
    @1
    @7
    @11
    eqid
    mgpplusg
    oveqi
    3eqtr3g
    grpidpropd
    cK
    @2
    @0
    @5
    @2
    eqid
    ringidval
    cL
    @3
    @1
    @7
    @3
    eqid
    ringidval
    3eqtr4g
end

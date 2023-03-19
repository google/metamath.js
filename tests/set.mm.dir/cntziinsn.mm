include "wss.mm"
include "cfv.mm"
include "cv.mm"
include "cplusg.mm"
include "co.mm"
include "wceq.mm"
include "wral.mm"
include "crab.mm"
include "csn.mm"
include "ciin.mm"
include "cin.mm"
include "eqid.mm"
include "cntzval.mm"
include "wcel.mm"
include "wa.mm"
include "ssel2.mm"
include "cntzsnval.mm"
include "syl.mm"
include "iineq2dv.mm"
include "ineq2d.mm"
include "riinrab.mm"
include "syl6eq.mm"
include "eqtr4d.mm"

theorem cntziinsn
  let vx: setvar x
  let cB: class B
  let cS: class S
  let cM: class M
  let cZ: class Z
  let vy: setvar y
  let vz: setvar z
  let cT: class T
  assume cntzrec.b: |- B = ( Base ` M )
  assume cntzrec.z: |- Z = ( Cntz ` M )

  disjoint B x
  disjoint M x
  disjoint S x
  disjoint Z x
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint B y
  disjoint B z
  disjoint M y
  disjoint M z
  disjoint S y
  disjoint S z
  disjoint T x
  disjoint T y
  disjoint Z y
  disjoint Z z
  assert |- ( S C_ B -> ( Z ` S ) = ( B i^i |^|_ x e. S ( Z ` { x } ) ) )

  proof
    cS
    cB
    wss
    #
    cS
    cZ
    cfv
    vy
    cv
    #
    vx
    cv
    #
    cM
    cplusg
    cfv
    #
    co
    @2
    @1
    @3
    co
    wceq
    #
    vx
    cS
    wral
    vy
    cB
    crab
    #
    cB
    vx
    cS
    @2
    csn
    cZ
    cfv
    #
    ciin
    #
    cin
    #
    vy
    vx
    cB
    @3
    cS
    cM
    cZ
    cntzrec.b
    @3
    eqid
    #
    cntzrec.z
    cntzval
    @0
    @8
    cB
    vx
    cS
    @4
    vy
    cB
    crab
    #
    ciin
    #
    cin
    @5
    @0
    @7
    @11
    cB
    @0
    vx
    cS
    @6
    @10
    @0
    @2
    cS
    wcel
    wa
    @2
    cB
    wcel
    @6
    @10
    wceq
    cS
    cB
    @2
    ssel2
    vy
    cB
    @3
    cM
    @2
    cZ
    cntzrec.b
    @9
    cntzrec.z
    cntzsnval
    syl
    iineq2dv
    ineq2d
    @4
    vx
    vy
    cB
    cS
    riinrab
    syl6eq
    eqtr4d
end

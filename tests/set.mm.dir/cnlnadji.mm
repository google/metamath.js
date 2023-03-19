include "cv.mm"
include "cfv.mm"
include "csp.mm"
include "co.mm"
include "wceq.mm"
include "chil.mm"
include "wral.mm"
include "crio.mm"
include "cmpt.mm"
include "eqid.mm"
include "oveq2.mm"
include "eqeq2d.mm"
include "ralbidv.mm"
include "cbvriotav.mm"
include "cnlnadjlem9.mm"

theorem cnlnadji
  let vx: setvar x
  let vy: setvar y
  let vt: setvar t
  let cT: class T
  let vf: setvar f
  let vg: setvar g
  let vv: setvar v
  let vw: setvar w
  let vz: setvar z
  assume cnlnadj.1: |- T e. LinOp
  assume cnlnadj.2: |- T e. ContOp

  disjoint t x
  disjoint t y
  disjoint T t
  disjoint x y
  disjoint T x
  disjoint T y
  disjoint f g
  disjoint f t
  disjoint f v
  disjoint f w
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint T f
  disjoint g t
  disjoint g v
  disjoint g w
  disjoint g x
  disjoint g y
  disjoint g z
  disjoint T g
  disjoint t v
  disjoint t w
  disjoint t z
  disjoint v w
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint T v
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint T w
  disjoint x z
  disjoint y z
  disjoint T z
  assert |- E. t e. ( LinOp i^i ContOp ) A. x e. ~H A. y e. ~H ( ( T ` x ) .ih y ) = ( x .ih ( t ` y ) )

  proof
    vx
    vz
    vy
    vw
    vv
    vt
    vv
    cv
    #
    cT
    cfv
    vz
    cv
    #
    csp
    co
    #
    @0
    vf
    cv
    #
    csp
    co
    #
    wceq
    #
    vv
    chil
    wral
    #
    vf
    chil
    crio
    #
    cT
    vg
    vz
    chil
    @7
    cmpt
    #
    vg
    chil
    vg
    cv
    cT
    cfv
    @1
    csp
    co
    cmpt
    #
    cnlnadj.1
    cnlnadj.2
    @9
    eqid
    @6
    @2
    @0
    vw
    cv
    #
    csp
    co
    #
    wceq
    #
    vv
    chil
    wral
    vf
    vw
    chil
    @3
    @10
    wceq
    #
    @5
    @12
    vv
    chil
    @13
    @4
    @11
    @2
    @3
    @10
    @0
    csp
    oveq2
    eqeq2d
    ralbidv
    cbvriotav
    @8
    eqid
    cnlnadjlem9
end

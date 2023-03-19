include "wss.mm"
include "cfv.mm"
include "wcel.mm"
include "cv.mm"
include "co.mm"
include "wceq.mm"
include "wral.mm"
include "crab.mm"
include "wa.mm"
include "cntzval.mm"
include "eleq2d.mm"
include "oveq1.mm"
include "oveq2.mm"
include "eqeq12d.mm"
include "ralbidv.mm"
include "elrab.mm"
include "syl6bb.mm"

theorem elcntz
  let vy: setvar y
  let cA: class A
  let cB: class B
  let c.pl: class .+
  let cS: class S
  let cM: class M
  let cZ: class Z
  let vm: setvar m
  let vs: setvar s
  let vx: setvar x
  let cT: class T
  let cX: class X
  let cY: class Y
  assume cntzfval.b: |- B = ( Base ` M )
  assume cntzfval.p: |- .+ = ( +g ` M )
  assume cntzfval.z: |- Z = ( Cntz ` M )

  disjoint .+ y
  disjoint A y
  disjoint M y
  disjoint S y
  disjoint m s
  disjoint m x
  disjoint m y
  disjoint .+ m
  disjoint s x
  disjoint s y
  disjoint .+ s
  disjoint x y
  disjoint .+ x
  disjoint A x
  disjoint B m
  disjoint B s
  disjoint B x
  disjoint M m
  disjoint M s
  disjoint M x
  disjoint T x
  disjoint T y
  disjoint S s
  disjoint S x
  disjoint X x
  disjoint X y
  disjoint Y x
  disjoint Y y
  assert |- ( S C_ B -> ( A e. ( Z ` S ) <-> ( A e. B /\ A. y e. S ( A .+ y ) = ( y .+ A ) ) ) )

  proof
    cS
    cB
    wss
    #
    cA
    cS
    cZ
    cfv
    #
    wcel
    cA
    vx
    cv
    #
    vy
    cv
    #
    c.pl
    co
    #
    @3
    @2
    c.pl
    co
    #
    wceq
    #
    vy
    cS
    wral
    #
    vx
    cB
    crab
    #
    wcel
    cA
    cB
    wcel
    cA
    @3
    c.pl
    co
    #
    @3
    cA
    c.pl
    co
    #
    wceq
    #
    vy
    cS
    wral
    #
    wa
    @0
    @1
    @8
    cA
    vx
    vy
    cB
    c.pl
    cS
    cM
    cZ
    cntzfval.b
    cntzfval.p
    cntzfval.z
    cntzval
    eleq2d
    @7
    @12
    vx
    cA
    cB
    @2
    cA
    wceq
    #
    @6
    @11
    vy
    cS
    @13
    @4
    @9
    @5
    @10
    @2
    cA
    @3
    c.pl
    oveq1
    @2
    cA
    @3
    c.pl
    oveq2
    eqeq12d
    ralbidv
    elrab
    syl6bb
end

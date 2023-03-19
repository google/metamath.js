include "wcel.mm"
include "csn.mm"
include "cfv.mm"
include "cv.mm"
include "co.mm"
include "wceq.mm"
include "wral.mm"
include "crab.mm"
include "wss.mm"
include "snssi.mm"
include "cntzval.mm"
include "syl.mm"
include "oveq2.mm"
include "oveq1.mm"
include "eqeq12d.mm"
include "ralsng.mm"
include "rabbidv.mm"
include "eqtrd.mm"

theorem cntzsnval
  let vx: setvar x
  let cB: class B
  let c.pl: class .+
  let cM: class M
  let cY: class Y
  let cZ: class Z
  let vm: setvar m
  let vs: setvar s
  let vy: setvar y
  let cA: class A
  let cT: class T
  let cS: class S
  let cX: class X
  assume cntzfval.b: |- B = ( Base ` M )
  assume cntzfval.p: |- .+ = ( +g ` M )
  assume cntzfval.z: |- Z = ( Cntz ` M )

  disjoint .+ x
  disjoint B x
  disjoint M x
  disjoint Y x
  disjoint m s
  disjoint m x
  disjoint m y
  disjoint .+ m
  disjoint s x
  disjoint s y
  disjoint .+ s
  disjoint x y
  disjoint .+ y
  disjoint A x
  disjoint A y
  disjoint B m
  disjoint B s
  disjoint M m
  disjoint M s
  disjoint M y
  disjoint T x
  disjoint T y
  disjoint S s
  disjoint S x
  disjoint S y
  disjoint X x
  disjoint X y
  disjoint Y y
  assert |- ( Y e. B -> ( Z ` { Y } ) = { x e. B | ( x .+ Y ) = ( Y .+ x ) } )

  proof
    cY
    cB
    wcel
    #
    cY
    csn
    #
    cZ
    cfv
    #
    vx
    cv
    #
    vy
    cv
    #
    c.pl
    co
    #
    @4
    @3
    c.pl
    co
    #
    wceq
    #
    vy
    @1
    wral
    #
    vx
    cB
    crab
    #
    @3
    cY
    c.pl
    co
    #
    cY
    @3
    c.pl
    co
    #
    wceq
    #
    vx
    cB
    crab
    @0
    @1
    cB
    wss
    @2
    @9
    wceq
    cY
    cB
    snssi
    vx
    vy
    cB
    c.pl
    @1
    cM
    cZ
    cntzfval.b
    cntzfval.p
    cntzfval.z
    cntzval
    syl
    @0
    @8
    @12
    vx
    cB
    @7
    @12
    vy
    cY
    cB
    @4
    cY
    wceq
    @5
    @10
    @6
    @11
    @4
    cY
    @3
    c.pl
    oveq2
    @4
    cY
    @3
    c.pl
    oveq1
    eqeq12d
    ralsng
    rabbidv
    eqtrd
end

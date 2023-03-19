include "wss.mm"
include "cfv.mm"
include "wcel.mm"
include "cv.mm"
include "co.mm"
include "wceq.mm"
include "wral.mm"
include "elcntz.mm"
include "baibd.mm"

theorem cntzel
  let vy: setvar y
  let cB: class B
  let c.pl: class .+
  let cS: class S
  let cM: class M
  let cX: class X
  let cZ: class Z
  let vm: setvar m
  let vs: setvar s
  let vx: setvar x
  let cA: class A
  let cT: class T
  let cY: class Y
  assume cntzfval.b: |- B = ( Base ` M )
  assume cntzfval.p: |- .+ = ( +g ` M )
  assume cntzfval.z: |- Z = ( Cntz ` M )

  disjoint .+ y
  disjoint M y
  disjoint S y
  disjoint X y
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
  disjoint A y
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
  disjoint Y x
  disjoint Y y
  assert |- ( ( S C_ B /\ X e. B ) -> ( X e. ( Z ` S ) <-> A. y e. S ( X .+ y ) = ( y .+ X ) ) )

  proof
    cS
    cB
    wss
    cX
    cS
    cZ
    cfv
    wcel
    cX
    cB
    wcel
    cX
    vy
    cv
    #
    c.pl
    co
    @0
    cX
    c.pl
    co
    wceq
    vy
    cS
    wral
    vy
    cX
    cB
    c.pl
    cS
    cM
    cZ
    cntzfval.b
    cntzfval.p
    cntzfval.z
    elcntz
    baibd
end

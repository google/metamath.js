include "wss.mm"
include "cfv.mm"
include "cv.mm"
include "co.mm"
include "wceq.mm"
include "wral.mm"
include "wa.mm"
include "crab.mm"
include "cntzval.mm"
include "sseq2d.mm"
include "ssrab.mm"
include "syl6bb.mm"
include "ibar.mm"
include "bicomd.mm"
include "sylan9bbr.mm"

theorem sscntz
  let vx: setvar x
  let vy: setvar y
  let cB: class B
  let c.pl: class .+
  let cS: class S
  let cT: class T
  let cM: class M
  let cZ: class Z
  let vm: setvar m
  let vs: setvar s
  let cA: class A
  let cX: class X
  let cY: class Y
  assume cntzfval.b: |- B = ( Base ` M )
  assume cntzfval.p: |- .+ = ( +g ` M )
  assume cntzfval.z: |- Z = ( Cntz ` M )

  disjoint x y
  disjoint .+ x
  disjoint .+ y
  disjoint B x
  disjoint M x
  disjoint M y
  disjoint T x
  disjoint T y
  disjoint S x
  disjoint S y
  disjoint m s
  disjoint m x
  disjoint m y
  disjoint .+ m
  disjoint s x
  disjoint s y
  disjoint .+ s
  disjoint A x
  disjoint A y
  disjoint B m
  disjoint B s
  disjoint M m
  disjoint M s
  disjoint S s
  disjoint X x
  disjoint X y
  disjoint Y x
  disjoint Y y
  assert |- ( ( S C_ B /\ T C_ B ) -> ( S C_ ( Z ` T ) <-> A. x e. S A. y e. T ( x .+ y ) = ( y .+ x ) ) )

  proof
    cT
    cB
    wss
    #
    cS
    cT
    cZ
    cfv
    #
    wss
    #
    cS
    cB
    wss
    #
    vx
    cv
    #
    vy
    cv
    #
    c.pl
    co
    @5
    @4
    c.pl
    co
    wceq
    vy
    cT
    wral
    #
    vx
    cS
    wral
    #
    wa
    #
    @3
    @7
    @0
    @2
    cS
    @6
    vx
    cB
    crab
    #
    wss
    @8
    @0
    @1
    @9
    cS
    vx
    vy
    cB
    c.pl
    cT
    cM
    cZ
    cntzfval.b
    cntzfval.p
    cntzfval.z
    cntzval
    sseq2d
    @6
    vx
    cB
    cS
    ssrab
    syl6bb
    @3
    @7
    @8
    @3
    @7
    ibar
    bicomd
    sylan9bbr
end

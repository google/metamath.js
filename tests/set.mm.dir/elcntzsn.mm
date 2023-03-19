include "wcel.mm"
include "csn.mm"
include "cfv.mm"
include "cv.mm"
include "co.mm"
include "wceq.mm"
include "crab.mm"
include "wa.mm"
include "cntzsnval.mm"
include "eleq2d.mm"
include "oveq1.mm"
include "oveq2.mm"
include "eqeq12d.mm"
include "elrab.mm"
include "syl6bb.mm"

theorem elcntzsn
  let cB: class B
  let c.pl: class .+
  let cM: class M
  let cX: class X
  let cY: class Y
  let cZ: class Z
  let vm: setvar m
  let vs: setvar s
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cT: class T
  let cS: class S
  assume cntzfval.b: |- B = ( Base ` M )
  assume cntzfval.p: |- .+ = ( +g ` M )
  assume cntzfval.z: |- Z = ( Cntz ` M )


  assert |- ( Y e. B -> ( X e. ( Z ` { Y } ) <-> ( X e. B /\ ( X .+ Y ) = ( Y .+ X ) ) ) )

  proof
    cY
    cB
    wcel
    #
    cX
    cY
    csn
    cZ
    cfv
    #
    wcel
    cX
    vx
    cv
    #
    cY
    c.pl
    co
    #
    cY
    @2
    c.pl
    co
    #
    wceq
    #
    vx
    cB
    crab
    #
    wcel
    cX
    cB
    wcel
    cX
    cY
    c.pl
    co
    #
    cY
    cX
    c.pl
    co
    #
    wceq
    #
    wa
    @0
    @1
    @6
    cX
    vx
    cB
    c.pl
    cM
    cY
    cZ
    cntzfval.b
    cntzfval.p
    cntzfval.z
    cntzsnval
    eleq2d
    @5
    @9
    vx
    cX
    cB
    @2
    cX
    wceq
    @3
    @7
    @4
    @8
    @2
    cX
    cY
    c.pl
    oveq1
    @2
    cX
    cY
    c.pl
    oveq2
    eqeq12d
    elrab
    syl6bb
end

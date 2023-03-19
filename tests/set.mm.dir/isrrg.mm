include "cv.mm"
include "co.mm"
include "wceq.mm"
include "wi.mm"
include "wral.mm"
include "oveq1.mm"
include "eqeq1d.mm"
include "imbi1d.mm"
include "ralbidv.mm"
include "rrgval.mm"
include "elrab2.mm"

theorem isrrg
  let vy: setvar y
  let cB: class B
  let cR: class R
  let c.x: class .x.
  let cE: class E
  let cX: class X
  let c.0: class .0.
  let vr: setvar r
  let vx: setvar x
  assume rrgval.e: |- E = ( RLReg ` R )
  assume rrgval.b: |- B = ( Base ` R )
  assume rrgval.t: |- .x. = ( .r ` R )
  assume rrgval.z: |- .0. = ( 0g ` R )

  disjoint B y
  disjoint R y
  disjoint X y
  disjoint B r
  disjoint B x
  disjoint r x
  disjoint r y
  disjoint x y
  disjoint R r
  disjoint R x
  disjoint .x. r
  disjoint .0. r
  disjoint .x. x
  disjoint X x
  disjoint .0. x
  assert |- ( X e. E <-> ( X e. B /\ A. y e. B ( ( X .x. y ) = .0. -> y = .0. ) ) )

  proof
    vx
    cv
    #
    vy
    cv
    #
    c.x
    co
    #
    c.0
    wceq
    #
    @1
    c.0
    wceq
    #
    wi
    #
    vy
    cB
    wral
    cX
    @1
    c.x
    co
    #
    c.0
    wceq
    #
    @4
    wi
    #
    vy
    cB
    wral
    vx
    cX
    cB
    cE
    @0
    cX
    wceq
    #
    @5
    @8
    vy
    cB
    @9
    @3
    @7
    @4
    @9
    @2
    @6
    c.0
    @0
    cX
    @1
    c.x
    oveq1
    eqeq1d
    imbi1d
    ralbidv
    vx
    vy
    cB
    cR
    c.x
    cE
    c.0
    rrgval.e
    rrgval.b
    rrgval.t
    rrgval.z
    rrgval
    elrab2
end

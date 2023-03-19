include "wcel.mm"
include "cv.mm"
include "co.mm"
include "wceq.mm"
include "wi.mm"
include "wral.mm"
include "isrrg.mm"
include "simprbi.mm"
include "oveq2.mm"
include "eqeq1d.mm"
include "eqeq1.mm"
include "imbi12d.mm"
include "rspcv.mm"
include "mpan9.mm"

theorem rrgeq0i
  let cB: class B
  let cR: class R
  let c.x: class .x.
  let cE: class E
  let cX: class X
  let cY: class Y
  let c.0: class .0.
  let vr: setvar r
  let vx: setvar x
  let vy: setvar y
  assume rrgval.e: |- E = ( RLReg ` R )
  assume rrgval.b: |- B = ( Base ` R )
  assume rrgval.t: |- .x. = ( .r ` R )
  assume rrgval.z: |- .0. = ( 0g ` R )


  assert |- ( ( X e. E /\ Y e. B ) -> ( ( X .x. Y ) = .0. -> Y = .0. ) )

  proof
    cX
    cE
    wcel
    #
    cX
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
    #
    cY
    cB
    wcel
    cX
    cY
    c.x
    co
    #
    c.0
    wceq
    #
    cY
    c.0
    wceq
    #
    wi
    #
    @0
    cX
    cB
    wcel
    @6
    vy
    cB
    cR
    c.x
    cE
    cX
    c.0
    rrgval.e
    rrgval.b
    rrgval.t
    rrgval.z
    isrrg
    simprbi
    @5
    @10
    vy
    cY
    cB
    @1
    cY
    wceq
    #
    @3
    @8
    @4
    @9
    @11
    @2
    @7
    c.0
    @1
    cY
    cX
    c.x
    oveq2
    eqeq1d
    @1
    cY
    c.0
    eqeq1
    imbi12d
    rspcv
    mpan9
end

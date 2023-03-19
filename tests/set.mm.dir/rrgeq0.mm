include "crg.mm"
include "wcel.mm"
include "w3a.mm"
include "co.mm"
include "wceq.mm"
include "wi.mm"
include "rrgeq0i.mm"
include "3adant1.mm"
include "simp1.mm"
include "cv.mm"
include "wral.mm"
include "crab.mm"
include "rrgval.mm"
include "ssrab2.mm"
include "eqsstri.mm"
include "simp2.mm"
include "sseldi.mm"
include "ringrz.mm"
include "syl2anc.mm"
include "oveq2.mm"
include "eqeq1d.mm"
include "syl5ibrcom.mm"
include "impbid.mm"

theorem rrgeq0
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


  assert |- ( ( R e. Ring /\ X e. E /\ Y e. B ) -> ( ( X .x. Y ) = .0. <-> Y = .0. ) )

  proof
    cR
    crg
    wcel
    #
    cX
    cE
    wcel
    #
    cY
    cB
    wcel
    #
    w3a
    #
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
    @1
    @2
    @5
    @6
    wi
    @0
    cB
    cR
    c.x
    cE
    cX
    cY
    c.0
    rrgval.e
    rrgval.b
    rrgval.t
    rrgval.z
    rrgeq0i
    3adant1
    @3
    @5
    @6
    cX
    c.0
    c.x
    co
    #
    c.0
    wceq
    #
    @3
    @0
    cX
    cB
    wcel
    @8
    @0
    @1
    @2
    simp1
    @3
    cE
    cB
    cX
    cE
    vx
    cv
    vy
    cv
    #
    c.x
    co
    c.0
    wceq
    @9
    c.0
    wceq
    wi
    vy
    cB
    wral
    #
    vx
    cB
    crab
    cB
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
    @10
    vx
    cB
    ssrab2
    eqsstri
    @0
    @1
    @2
    simp2
    sseldi
    cB
    cR
    c.x
    cX
    c.0
    rrgval.b
    rrgval.t
    rrgval.z
    ringrz
    syl2anc
    @6
    @4
    @7
    c.0
    cY
    c.0
    cX
    c.x
    oveq2
    eqeq1d
    syl5ibrcom
    impbid
end

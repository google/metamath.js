include "casa.mm"
include "wcel.mm"
include "cv.mm"
include "co.mm"
include "wceq.mm"
include "wa.mm"
include "wral.mm"
include "w3a.mm"
include "clmod.mm"
include "crg.mm"
include "ccrg.mm"
include "isassa.mm"
include "simprbi.mm"
include "oveq1.mm"
include "oveq1d.mm"
include "eqeq12d.mm"
include "oveq2d.mm"
include "anbi12d.mm"
include "oveq2.mm"
include "rspc3v.mm"
include "mpan9.mm"

theorem assalem
  let cA: class A
  let cB: class B
  let c.x: class .x.
  let c.xp: class .X.
  let cF: class F
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  let vr: setvar r
  let vx: setvar x
  let vy: setvar y
  let vf: setvar f
  let vw: setvar w
  let vs: setvar s
  let vt: setvar t
  assume isassa.v: |- V = ( Base ` W )
  assume isassa.f: |- F = ( Scalar ` W )
  assume isassa.b: |- B = ( Base ` F )
  assume isassa.s: |- .x. = ( .s ` W )
  assume isassa.t: |- .X. = ( .r ` W )


  assert |- ( ( W e. AssAlg /\ ( A e. B /\ X e. V /\ Y e. V ) ) -> ( ( ( A .x. X ) .X. Y ) = ( A .x. ( X .X. Y ) ) /\ ( X .X. ( A .x. Y ) ) = ( A .x. ( X .X. Y ) ) ) )

  proof
    cW
    casa
    wcel
    #
    vr
    cv
    #
    vx
    cv
    #
    c.x
    co
    #
    vy
    cv
    #
    c.xp
    co
    #
    @1
    @2
    @4
    c.xp
    co
    #
    c.x
    co
    #
    wceq
    #
    @2
    @1
    @4
    c.x
    co
    #
    c.xp
    co
    #
    @7
    wceq
    #
    wa
    #
    vy
    cV
    wral
    vx
    cV
    wral
    vr
    cB
    wral
    #
    cA
    cB
    wcel
    cX
    cV
    wcel
    cY
    cV
    wcel
    w3a
    cA
    cX
    c.x
    co
    #
    cY
    c.xp
    co
    #
    cA
    cX
    cY
    c.xp
    co
    #
    c.x
    co
    #
    wceq
    #
    cX
    cA
    cY
    c.x
    co
    #
    c.xp
    co
    #
    @17
    wceq
    #
    wa
    #
    @0
    cW
    clmod
    wcel
    cW
    crg
    wcel
    cF
    ccrg
    wcel
    w3a
    @13
    vx
    vy
    cB
    c.x
    c.xp
    cF
    cV
    cW
    vr
    isassa.v
    isassa.f
    isassa.b
    isassa.s
    isassa.t
    isassa
    simprbi
    @12
    @22
    cA
    @2
    c.x
    co
    #
    @4
    c.xp
    co
    #
    cA
    @6
    c.x
    co
    #
    wceq
    #
    @2
    cA
    @4
    c.x
    co
    #
    c.xp
    co
    #
    @25
    wceq
    #
    wa
    @14
    @4
    c.xp
    co
    #
    cA
    cX
    @4
    c.xp
    co
    #
    c.x
    co
    #
    wceq
    #
    cX
    @27
    c.xp
    co
    #
    @32
    wceq
    #
    wa
    vr
    vx
    vy
    cA
    cX
    cY
    cB
    cV
    cV
    @1
    cA
    wceq
    #
    @8
    @26
    @11
    @29
    @36
    @5
    @24
    @7
    @25
    @36
    @3
    @23
    @4
    c.xp
    @1
    cA
    @2
    c.x
    oveq1
    oveq1d
    @1
    cA
    @6
    c.x
    oveq1
    #
    eqeq12d
    @36
    @10
    @28
    @7
    @25
    @36
    @9
    @27
    @2
    c.xp
    @1
    cA
    @4
    c.x
    oveq1
    oveq2d
    @37
    eqeq12d
    anbi12d
    @2
    cX
    wceq
    #
    @26
    @33
    @29
    @35
    @38
    @24
    @30
    @25
    @32
    @38
    @23
    @14
    @4
    c.xp
    @2
    cX
    cA
    c.x
    oveq2
    oveq1d
    @38
    @6
    @31
    cA
    c.x
    @2
    cX
    @4
    c.xp
    oveq1
    oveq2d
    #
    eqeq12d
    @38
    @28
    @34
    @25
    @32
    @2
    cX
    @27
    c.xp
    oveq1
    @39
    eqeq12d
    anbi12d
    @4
    cY
    wceq
    #
    @33
    @18
    @35
    @21
    @40
    @30
    @15
    @32
    @17
    @4
    cY
    @14
    c.xp
    oveq2
    @40
    @31
    @16
    cA
    c.x
    @4
    cY
    cX
    c.xp
    oveq2
    oveq2d
    #
    eqeq12d
    @40
    @34
    @20
    @32
    @17
    @40
    @27
    @19
    cX
    c.xp
    @4
    cY
    cA
    c.x
    oveq2
    oveq2d
    @41
    eqeq12d
    anbi12d
    rspc3v
    mpan9
end

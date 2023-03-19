include "wcel.mm"
include "w3a.mm"
include "cv.mm"
include "co.mm"
include "cfv.mm"
include "wceq.mm"
include "wral.mm"
include "wf.mm"
include "islfl.mm"
include "simplbda.mm"
include "3adant3.mm"
include "wi.mm"
include "oveq1.mm"
include "oveq1d.mm"
include "fveq2d.mm"
include "eqeq12d.mm"
include "oveq2.mm"
include "fveq2.mm"
include "oveq2d.mm"
include "rspc3v.mm"
include "3ad2ant3.mm"
include "mpd.mm"

theorem lfli
  let cD: class D
  let c.pl: class .+
  let c.pd: class .+^
  let cR: class R
  let c.x: class .x.
  let c.xp: class .X.
  let cF: class F
  let cG: class G
  let cK: class K
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  let cZ: class Z
  let vw: setvar w
  let vf: setvar f
  let vr: setvar r
  let vx: setvar x
  let vy: setvar y
  assume lflset.v: |- V = ( Base ` W )
  assume lflset.a: |- .+ = ( +g ` W )
  assume lflset.d: |- D = ( Scalar ` W )
  assume lflset.s: |- .x. = ( .s ` W )
  assume lflset.k: |- K = ( Base ` D )
  assume lflset.p: |- .+^ = ( +g ` D )
  assume lflset.t: |- .X. = ( .r ` D )
  assume lflset.f: |- F = ( LFnl ` W )


  assert |- ( ( W e. Z /\ G e. F /\ ( R e. K /\ X e. V /\ Y e. V ) ) -> ( G ` ( ( R .x. X ) .+ Y ) ) = ( ( R .X. ( G ` X ) ) .+^ ( G ` Y ) ) )

  proof
    cW
    cZ
    wcel
    #
    cG
    cF
    wcel
    #
    cR
    cK
    wcel
    cX
    cV
    wcel
    cY
    cV
    wcel
    w3a
    #
    w3a
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
    c.pl
    co
    #
    cG
    cfv
    #
    @3
    @4
    cG
    cfv
    #
    c.xp
    co
    #
    @6
    cG
    cfv
    #
    c.pd
    co
    #
    wceq
    #
    vy
    cV
    wral
    vx
    cV
    wral
    vr
    cK
    wral
    #
    cR
    cX
    c.x
    co
    #
    cY
    c.pl
    co
    #
    cG
    cfv
    #
    cR
    cX
    cG
    cfv
    #
    c.xp
    co
    #
    cY
    cG
    cfv
    #
    c.pd
    co
    #
    wceq
    #
    @0
    @1
    @14
    @2
    @0
    @1
    cV
    cK
    cG
    wf
    @14
    vx
    vy
    cD
    c.pl
    c.pd
    c.x
    c.xp
    cF
    cG
    cK
    cV
    cW
    cZ
    vr
    lflset.v
    lflset.a
    lflset.d
    lflset.s
    lflset.k
    lflset.p
    lflset.t
    lflset.f
    islfl
    simplbda
    3adant3
    @2
    @0
    @14
    @22
    wi
    @1
    @13
    @22
    cR
    @4
    c.x
    co
    #
    @6
    c.pl
    co
    #
    cG
    cfv
    #
    cR
    @9
    c.xp
    co
    #
    @11
    c.pd
    co
    #
    wceq
    @15
    @6
    c.pl
    co
    #
    cG
    cfv
    #
    @19
    @11
    c.pd
    co
    #
    wceq
    vr
    vx
    vy
    cR
    cX
    cY
    cK
    cV
    cV
    @3
    cR
    wceq
    #
    @8
    @25
    @12
    @27
    @31
    @7
    @24
    cG
    @31
    @5
    @23
    @6
    c.pl
    @3
    cR
    @4
    c.x
    oveq1
    oveq1d
    fveq2d
    @31
    @10
    @26
    @11
    c.pd
    @3
    cR
    @9
    c.xp
    oveq1
    oveq1d
    eqeq12d
    @4
    cX
    wceq
    #
    @25
    @29
    @27
    @30
    @32
    @24
    @28
    cG
    @32
    @23
    @15
    @6
    c.pl
    @4
    cX
    cR
    c.x
    oveq2
    oveq1d
    fveq2d
    @32
    @26
    @19
    @11
    c.pd
    @32
    @9
    @18
    cR
    c.xp
    @4
    cX
    cG
    fveq2
    oveq2d
    oveq1d
    eqeq12d
    @6
    cY
    wceq
    #
    @29
    @17
    @30
    @21
    @33
    @28
    @16
    cG
    @6
    cY
    @15
    c.pl
    oveq2
    fveq2d
    @33
    @11
    @20
    @19
    c.pd
    @6
    cY
    cG
    fveq2
    oveq2d
    eqeq12d
    rspc3v
    3ad2ant3
    mpd
end

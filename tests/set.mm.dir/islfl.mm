include "wcel.mm"
include "cv.mm"
include "co.mm"
include "cfv.mm"
include "wceq.mm"
include "wral.mm"
include "cmap.mm"
include "crab.mm"
include "wf.mm"
include "wa.mm"
include "lflset.mm"
include "eleq2d.mm"
include "fveq1.mm"
include "oveq2d.mm"
include "oveq12d.mm"
include "eqeq12d.mm"
include "2ralbidv.mm"
include "ralbidv.mm"
include "elrab.mm"
include "cbs.mm"
include "cvv.mm"
include "fvex.mm"
include "eqeltri.mm"
include "elmap.mm"
include "anbi1i.mm"
include "bitri.mm"
include "syl6bb.mm"

theorem islfl
  let vx: setvar x
  let vy: setvar y
  let cD: class D
  let c.pl: class .+
  let c.pd: class .+^
  let c.x: class .x.
  let c.xp: class .X.
  let cF: class F
  let cG: class G
  let cK: class K
  let cV: class V
  let cW: class W
  let cX: class X
  let vr: setvar r
  let vw: setvar w
  let vf: setvar f
  assume lflset.v: |- V = ( Base ` W )
  assume lflset.a: |- .+ = ( +g ` W )
  assume lflset.d: |- D = ( Scalar ` W )
  assume lflset.s: |- .x. = ( .s ` W )
  assume lflset.k: |- K = ( Base ` D )
  assume lflset.p: |- .+^ = ( +g ` D )
  assume lflset.t: |- .X. = ( .r ` D )
  assume lflset.f: |- F = ( LFnl ` W )

  disjoint K r
  disjoint x y
  disjoint V x
  disjoint V y
  disjoint r x
  disjoint r y
  disjoint W r
  disjoint W x
  disjoint W y
  disjoint G r
  disjoint G x
  disjoint G y
  disjoint .+^ w
  disjoint f r
  disjoint f w
  disjoint K f
  disjoint r w
  disjoint K w
  disjoint f x
  disjoint f y
  disjoint V f
  disjoint w x
  disjoint w y
  disjoint V w
  disjoint W f
  disjoint W w
  disjoint .x. w
  disjoint .+ w
  disjoint .X. w
  disjoint .+ f
  disjoint G f
  disjoint .+^ f
  disjoint .x. f
  disjoint .X. f
  assert |- ( W e. X -> ( G e. F <-> ( G : V --> K /\ A. r e. K A. x e. V A. y e. V ( G ` ( ( r .x. x ) .+ y ) ) = ( ( r .X. ( G ` x ) ) .+^ ( G ` y ) ) ) ) )

  proof
    cW
    cX
    wcel
    #
    cG
    cF
    wcel
    cG
    vr
    cv
    #
    vx
    cv
    #
    c.x
    co
    vy
    cv
    #
    c.pl
    co
    #
    vf
    cv
    #
    cfv
    #
    @1
    @2
    @5
    cfv
    #
    c.xp
    co
    #
    @3
    @5
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
    #
    vr
    cK
    wral
    #
    vf
    cK
    cV
    cmap
    co
    #
    crab
    #
    wcel
    #
    cV
    cK
    cG
    wf
    #
    @4
    cG
    cfv
    #
    @1
    @2
    cG
    cfv
    #
    c.xp
    co
    #
    @3
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
    #
    vr
    cK
    wral
    #
    wa
    #
    @0
    cF
    @15
    cG
    vx
    vy
    cD
    c.pl
    c.pd
    c.x
    c.xp
    vf
    cF
    cK
    cV
    cW
    cX
    vr
    lflset.v
    lflset.a
    lflset.d
    lflset.s
    lflset.k
    lflset.p
    lflset.t
    lflset.f
    lflset
    eleq2d
    @16
    cG
    @14
    wcel
    #
    @25
    wa
    @26
    @13
    @25
    vf
    cG
    @14
    @5
    cG
    wceq
    #
    @12
    @24
    vr
    cK
    @28
    @11
    @23
    vx
    vy
    cV
    cV
    @28
    @6
    @18
    @10
    @22
    @4
    @5
    cG
    fveq1
    @28
    @8
    @20
    @9
    @21
    c.pd
    @28
    @7
    @19
    @1
    c.xp
    @2
    @5
    cG
    fveq1
    oveq2d
    @3
    @5
    cG
    fveq1
    oveq12d
    eqeq12d
    2ralbidv
    ralbidv
    elrab
    @27
    @17
    @25
    cK
    cV
    cG
    cK
    cD
    cbs
    cfv
    cvv
    lflset.k
    cD
    cbs
    fvex
    eqeltri
    cV
    cW
    cbs
    cfv
    cvv
    lflset.v
    cW
    cbs
    fvex
    eqeltri
    elmap
    anbi1i
    bitri
    syl6bb
end

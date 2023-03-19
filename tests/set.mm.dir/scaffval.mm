include "cscaf.mm"
include "cfv.mm"
include "cv.mm"
include "co.mm"
include "cmpt2.mm"
include "cvv.mm"
include "wcel.mm"
include "wceq.mm"
include "csca.mm"
include "cbs.mm"
include "cvsca.mm"
include "fveq2.mm"
include "syl6eqr.mm"
include "fveq2d.mm"
include "oveqd.mm"
include "mpt2eq123dv.mm"
include "df-scaf.mm"
include "cxp.mm"
include "crn.mm"
include "c0.mm"
include "csn.mm"
include "cun.mm"
include "wf.mm"
include "wral.mm"
include "cop.mm"
include "df-ov.mm"
include "fvrn0.mm"
include "eqeltri.mm"
include "rgen2w.mm"
include "eqid.mm"
include "fmpt2.mm"
include "mpbi.mm"
include "fvex.mm"
include "xpex.mm"
include "rnex.mm"
include "p0ex.mm"
include "unex.mm"
include "fex2.mm"
include "mp3an.mm"
include "fvmpt.mm"
include "wn.mm"
include "fvprc.mm"
include "mpt20.mm"
include "syl5eq.mm"
include "base0.mm"
include "mpt2eq12.mm"
include "sylancl.mm"
include "eqtr4d.mm"
include "pm2.61i.mm"
include "eqtri.mm"

theorem scaffval
  let vx: setvar x
  let vy: setvar y
  let cB: class B
  let c.xb: class .xb
  let c.x: class .x.
  let cF: class F
  let cK: class K
  let cW: class W
  let vw: setvar w
  let cX: class X
  let cY: class Y
  assume scaffval.b: |- B = ( Base ` W )
  assume scaffval.f: |- F = ( Scalar ` W )
  assume scaffval.k: |- K = ( Base ` F )
  assume scaffval.a: |- .xb = ( .sf ` W )
  assume scaffval.s: |- .x. = ( .s ` W )

  disjoint x y
  disjoint B x
  disjoint B y
  disjoint K x
  disjoint K y
  disjoint .x. x
  disjoint .x. y
  disjoint W x
  disjoint W y
  disjoint w x
  disjoint w y
  disjoint B w
  disjoint K w
  disjoint .x. w
  disjoint W w
  disjoint X x
  disjoint X y
  disjoint Y x
  disjoint Y y
  assert |- .xb = ( x e. K , y e. B |-> ( x .x. y ) )

  proof
    c.xb
    cW
    cscaf
    cfv
    #
    vx
    vy
    cK
    cB
    vx
    cv
    #
    vy
    cv
    #
    c.x
    co
    #
    cmpt2
    #
    scaffval.a
    cW
    cvv
    wcel
    #
    @0
    @4
    wceq
    vw
    cW
    vx
    vy
    vw
    cv
    #
    csca
    cfv
    #
    cbs
    cfv
    #
    @6
    cbs
    cfv
    #
    @1
    @2
    @6
    cvsca
    cfv
    #
    co
    #
    cmpt2
    @4
    cvv
    cscaf
    @6
    cW
    wceq
    #
    vx
    vy
    @8
    @9
    @11
    cK
    cB
    @3
    @12
    @8
    cF
    cbs
    cfv
    #
    cK
    @12
    @7
    cF
    cbs
    @12
    @7
    cW
    csca
    cfv
    #
    cF
    @6
    cW
    csca
    fveq2
    scaffval.f
    syl6eqr
    fveq2d
    scaffval.k
    syl6eqr
    @12
    @9
    cW
    cbs
    cfv
    #
    cB
    @6
    cW
    cbs
    fveq2
    scaffval.b
    syl6eqr
    @12
    @10
    c.x
    @1
    @2
    @12
    @10
    cW
    cvsca
    cfv
    #
    c.x
    @6
    cW
    cvsca
    fveq2
    scaffval.s
    syl6eqr
    oveqd
    mpt2eq123dv
    vx
    vy
    vw
    df-scaf
    cK
    cB
    cxp
    #
    c.x
    crn
    #
    c0
    csn
    #
    cun
    #
    @4
    wf
    #
    @17
    cvv
    wcel
    @20
    cvv
    wcel
    @4
    cvv
    wcel
    @3
    @20
    wcel
    #
    vy
    cB
    wral
    vx
    cK
    wral
    @21
    @22
    vx
    vy
    cK
    cB
    @3
    @1
    @2
    cop
    #
    c.x
    cfv
    @20
    @1
    @2
    c.x
    df-ov
    c.x
    @23
    fvrn0
    eqeltri
    rgen2w
    vx
    vy
    cK
    cB
    @3
    @20
    @4
    @4
    eqid
    fmpt2
    mpbi
    cK
    cB
    cK
    @13
    cvv
    scaffval.k
    cF
    cbs
    fvex
    eqeltri
    cB
    @15
    cvv
    scaffval.b
    cW
    cbs
    fvex
    eqeltri
    xpex
    @18
    @19
    c.x
    c.x
    @16
    cvv
    scaffval.s
    cW
    cvsca
    fvex
    eqeltri
    rnex
    p0ex
    unex
    @17
    @20
    @4
    cvv
    cvv
    fex2
    mp3an
    fvmpt
    @5
    wn
    #
    @0
    vx
    vy
    c0
    cB
    @3
    cmpt2
    #
    @4
    @24
    @0
    c0
    @25
    cW
    cscaf
    fvprc
    vx
    vy
    cB
    @3
    mpt20
    syl6eqr
    @24
    cK
    c0
    wceq
    cB
    cB
    wceq
    @4
    @25
    wceq
    @24
    cK
    c0
    cbs
    cfv
    #
    c0
    @24
    cK
    @13
    @26
    scaffval.k
    @24
    cF
    c0
    cbs
    @24
    cF
    @14
    c0
    scaffval.f
    cW
    csca
    fvprc
    syl5eq
    fveq2d
    syl5eq
    base0
    syl6eqr
    cB
    eqid
    vx
    vy
    cK
    cB
    c0
    cB
    @3
    mpt2eq12
    sylancl
    eqtr4d
    pm2.61i
    eqtri
end

include "cipf.mm"
include "cfv.mm"
include "cv.mm"
include "co.mm"
include "cmpt2.mm"
include "cvv.mm"
include "wcel.mm"
include "wceq.mm"
include "cbs.mm"
include "cip.mm"
include "fveq2.mm"
include "syl6eqr.mm"
include "oveqd.mm"
include "mpt2eq123dv.mm"
include "df-ipf.mm"
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
include "mpt2eq12.mm"
include "syl2anc.mm"
include "eqtr4d.mm"
include "pm2.61i.mm"
include "eqtri.mm"

theorem ipffval
  let vx: setvar x
  let vy: setvar y
  let c.x: class .x.
  let c.xi: class .,
  let cV: class V
  let cW: class W
  let vg: setvar g
  let cX: class X
  let cY: class Y
  assume ipffval.1: |- V = ( Base ` W )
  assume ipffval.2: |- ., = ( .i ` W )
  assume ipffval.3: |- .x. = ( .if ` W )

  disjoint x y
  disjoint ., x
  disjoint ., y
  disjoint V x
  disjoint V y
  disjoint W x
  disjoint W y
  disjoint g x
  disjoint g y
  disjoint ., g
  disjoint V g
  disjoint W g
  disjoint X x
  disjoint X y
  disjoint Y x
  disjoint Y y
  assert |- .x. = ( x e. V , y e. V |-> ( x ., y ) )

  proof
    c.x
    cW
    cipf
    cfv
    #
    vx
    vy
    cV
    cV
    vx
    cv
    #
    vy
    cv
    #
    c.xi
    co
    #
    cmpt2
    #
    ipffval.3
    cW
    cvv
    wcel
    #
    @0
    @4
    wceq
    vg
    cW
    vx
    vy
    vg
    cv
    #
    cbs
    cfv
    #
    @7
    @1
    @2
    @6
    cip
    cfv
    #
    co
    #
    cmpt2
    @4
    cvv
    cipf
    @6
    cW
    wceq
    #
    vx
    vy
    @7
    @7
    @9
    cV
    cV
    @3
    @10
    @7
    cW
    cbs
    cfv
    #
    cV
    @6
    cW
    cbs
    fveq2
    ipffval.1
    syl6eqr
    #
    @12
    @10
    @8
    c.xi
    @1
    @2
    @10
    @8
    cW
    cip
    cfv
    #
    c.xi
    @6
    cW
    cip
    fveq2
    ipffval.2
    syl6eqr
    oveqd
    mpt2eq123dv
    vx
    vy
    vg
    df-ipf
    cV
    cV
    cxp
    #
    c.xi
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
    @14
    cvv
    wcel
    @17
    cvv
    wcel
    @4
    cvv
    wcel
    @3
    @17
    wcel
    #
    vy
    cV
    wral
    vx
    cV
    wral
    @18
    @19
    vx
    vy
    cV
    cV
    @3
    @1
    @2
    cop
    #
    c.xi
    cfv
    @17
    @1
    @2
    c.xi
    df-ov
    c.xi
    @20
    fvrn0
    eqeltri
    rgen2w
    vx
    vy
    cV
    cV
    @3
    @17
    @4
    @4
    eqid
    fmpt2
    mpbi
    cV
    cV
    cV
    @11
    cvv
    ipffval.1
    cW
    cbs
    fvex
    eqeltri
    #
    @21
    xpex
    @15
    @16
    c.xi
    c.xi
    @13
    cvv
    ipffval.2
    cW
    cip
    fvex
    eqeltri
    rnex
    p0ex
    unex
    @14
    @17
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
    c0
    @3
    cmpt2
    #
    @4
    @22
    @0
    c0
    @23
    cW
    cipf
    fvprc
    vx
    vy
    c0
    @3
    mpt20
    syl6eqr
    @22
    cV
    c0
    wceq
    #
    @24
    @4
    @23
    wceq
    @22
    cV
    @11
    c0
    ipffval.1
    cW
    cbs
    fvprc
    syl5eq
    #
    @25
    vx
    vy
    cV
    cV
    c0
    c0
    @3
    mpt2eq12
    syl2anc
    eqtr4d
    pm2.61i
    eqtri
end

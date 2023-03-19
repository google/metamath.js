include "cplusf.mm"
include "cfv.mm"
include "cv.mm"
include "co.mm"
include "cmpt2.mm"
include "cvv.mm"
include "wcel.mm"
include "wceq.mm"
include "cbs.mm"
include "cplusg.mm"
include "fveq2.mm"
include "syl6eqr.mm"
include "oveqd.mm"
include "mpt2eq123dv.mm"
include "df-plusf.mm"
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

theorem plusffval
  let vx: setvar x
  let vy: setvar y
  let cB: class B
  let c.pl: class .+
  let c.pd: class .+^
  let cG: class G
  let vg: setvar g
  let cX: class X
  let cY: class Y
  assume plusffval.1: |- B = ( Base ` G )
  assume plusffval.2: |- .+ = ( +g ` G )
  assume plusffval.3: |- .+^ = ( +f ` G )

  disjoint x y
  disjoint B x
  disjoint B y
  disjoint G x
  disjoint G y
  disjoint .+ x
  disjoint .+ y
  disjoint g x
  disjoint g y
  disjoint B g
  disjoint G g
  disjoint .+ g
  disjoint X x
  disjoint X y
  disjoint Y x
  disjoint Y y
  assert |- .+^ = ( x e. B , y e. B |-> ( x .+ y ) )

  proof
    c.pd
    cG
    cplusf
    cfv
    #
    vx
    vy
    cB
    cB
    vx
    cv
    #
    vy
    cv
    #
    c.pl
    co
    #
    cmpt2
    #
    plusffval.3
    cG
    cvv
    wcel
    #
    @0
    @4
    wceq
    vg
    cG
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
    cplusg
    cfv
    #
    co
    #
    cmpt2
    @4
    cvv
    cplusf
    @6
    cG
    wceq
    #
    vx
    vy
    @7
    @7
    @9
    cB
    cB
    @3
    @10
    @7
    cG
    cbs
    cfv
    #
    cB
    @6
    cG
    cbs
    fveq2
    plusffval.1
    syl6eqr
    #
    @12
    @10
    @8
    c.pl
    @1
    @2
    @10
    @8
    cG
    cplusg
    cfv
    #
    c.pl
    @6
    cG
    cplusg
    fveq2
    plusffval.2
    syl6eqr
    oveqd
    mpt2eq123dv
    vx
    vy
    vg
    df-plusf
    cB
    cB
    cxp
    #
    c.pl
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
    cB
    wral
    vx
    cB
    wral
    @18
    @19
    vx
    vy
    cB
    cB
    @3
    @1
    @2
    cop
    #
    c.pl
    cfv
    @17
    @1
    @2
    c.pl
    df-ov
    c.pl
    @20
    fvrn0
    eqeltri
    rgen2w
    vx
    vy
    cB
    cB
    @3
    @17
    @4
    @4
    eqid
    fmpt2
    mpbi
    cB
    cB
    cB
    @11
    cvv
    plusffval.1
    cG
    cbs
    fvex
    eqeltri
    #
    @21
    xpex
    @15
    @16
    c.pl
    c.pl
    @13
    cvv
    plusffval.2
    cG
    cplusg
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
    cG
    cplusf
    fvprc
    vx
    vy
    c0
    @3
    mpt20
    syl6eqr
    @22
    cB
    c0
    wceq
    #
    @24
    @4
    @23
    wceq
    @22
    cB
    @11
    c0
    plusffval.1
    cG
    cbs
    fvprc
    syl5eq
    #
    @25
    vx
    vy
    cB
    cB
    c0
    c0
    @3
    mpt2eq12
    syl2anc
    eqtr4d
    pm2.61i
    eqtri
end

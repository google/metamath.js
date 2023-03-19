include "cstf.mm"
include "cfv.mm"
include "cv.mm"
include "cmpt.mm"
include "cvv.mm"
include "wcel.mm"
include "wceq.mm"
include "cbs.mm"
include "cstv.mm"
include "fveq2.mm"
include "syl6eqr.mm"
include "fveq1d.mm"
include "mpteq12dv.mm"
include "df-staf.mm"
include "crn.mm"
include "c0.mm"
include "csn.mm"
include "cun.mm"
include "wf.mm"
include "eqid.mm"
include "fvrn0.mm"
include "a1i.mm"
include "fmpti.mm"
include "fvex.mm"
include "eqeltri.mm"
include "rnex.mm"
include "p0ex.mm"
include "unex.mm"
include "fex2.mm"
include "mp3an.mm"
include "fvmpt.mm"
include "wn.mm"
include "fvprc.mm"
include "mpt0.mm"
include "syl5eq.mm"
include "mpteq1d.mm"
include "eqtr4d.mm"
include "pm2.61i.mm"
include "eqtri.mm"

theorem staffval
  let vx: setvar x
  let cB: class B
  let cR: class R
  let c.xb: class .xb
  let c.as: class .*
  let cA: class A
  let vf: setvar f
  assume staffval.b: |- B = ( Base ` R )
  assume staffval.i: |- .* = ( *r ` R )
  assume staffval.f: |- .xb = ( *rf ` R )

  disjoint B x
  disjoint .* x
  disjoint R x
  disjoint A x
  disjoint f x
  disjoint B f
  disjoint .* f
  disjoint R f
  assert |- .xb = ( x e. B |-> ( .* ` x ) )

  proof
    c.xb
    cR
    cstf
    cfv
    #
    vx
    cB
    vx
    cv
    #
    c.as
    cfv
    #
    cmpt
    #
    staffval.f
    cR
    cvv
    wcel
    #
    @0
    @3
    wceq
    vf
    cR
    vx
    vf
    cv
    #
    cbs
    cfv
    #
    @1
    @5
    cstv
    cfv
    #
    cfv
    #
    cmpt
    @3
    cvv
    cstf
    @5
    cR
    wceq
    #
    vx
    @6
    @8
    cB
    @2
    @9
    @6
    cR
    cbs
    cfv
    #
    cB
    @5
    cR
    cbs
    fveq2
    staffval.b
    syl6eqr
    @9
    @1
    @7
    c.as
    @9
    @7
    cR
    cstv
    cfv
    #
    c.as
    @5
    cR
    cstv
    fveq2
    staffval.i
    syl6eqr
    fveq1d
    mpteq12dv
    vx
    vf
    df-staf
    cB
    c.as
    crn
    #
    c0
    csn
    #
    cun
    #
    @3
    wf
    cB
    cvv
    wcel
    @14
    cvv
    wcel
    @3
    cvv
    wcel
    vx
    cB
    @14
    @2
    @3
    @3
    eqid
    @2
    @14
    wcel
    @1
    cB
    wcel
    c.as
    @1
    fvrn0
    a1i
    fmpti
    cB
    @10
    cvv
    staffval.b
    cR
    cbs
    fvex
    eqeltri
    @12
    @13
    c.as
    c.as
    @11
    cvv
    staffval.i
    cR
    cstv
    fvex
    eqeltri
    rnex
    p0ex
    unex
    cB
    @14
    @3
    cvv
    cvv
    fex2
    mp3an
    fvmpt
    @4
    wn
    #
    @0
    vx
    c0
    @2
    cmpt
    #
    @3
    @15
    @0
    c0
    @16
    cR
    cstf
    fvprc
    vx
    @2
    mpt0
    syl6eqr
    @15
    vx
    cB
    c0
    @2
    @15
    cB
    @10
    c0
    staffval.b
    cR
    cbs
    fvprc
    syl5eq
    mpteq1d
    eqtr4d
    pm2.61i
    eqtri
end

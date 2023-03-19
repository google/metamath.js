include "cascl.mm"
include "cfv.mm"
include "cv.mm"
include "co.mm"
include "cmpt.mm"
include "cvv.mm"
include "wcel.mm"
include "wceq.mm"
include "csca.mm"
include "cbs.mm"
include "cur.mm"
include "cvsca.mm"
include "fveq2.mm"
include "syl6eqr.mm"
include "fveq2d.mm"
include "eqidd.mm"
include "oveq123d.mm"
include "mpteq12dv.mm"
include "df-ascl.mm"
include "fveq2i.mm"
include "eqtri.mm"
include "fvex.mm"
include "eqeltri.mm"
include "mptex.mm"
include "fvmpt.mm"
include "wn.mm"
include "c0.mm"
include "fvprc.mm"
include "mpt0.mm"
include "syl5eq.mm"
include "base0.mm"
include "mpteq1d.mm"
include "eqtr4d.mm"
include "pm2.61i.mm"

theorem asclfval
  let vx: setvar x
  let cA: class A
  let c.x: class .x.
  let c.1: class .1.
  let cF: class F
  let cK: class K
  let cW: class W
  let vw: setvar w
  let cX: class X
  assume asclfval.a: |- A = ( algSc ` W )
  assume asclfval.f: |- F = ( Scalar ` W )
  assume asclfval.k: |- K = ( Base ` F )
  assume asclfval.s: |- .x. = ( .s ` W )
  assume asclfval.o: |- .1. = ( 1r ` W )

  disjoint K x
  disjoint .1. x
  disjoint .x. x
  disjoint W x
  disjoint w x
  disjoint K w
  disjoint .1. w
  disjoint .x. w
  disjoint W w
  disjoint X x
  assert |- A = ( x e. K |-> ( x .x. .1. ) )

  proof
    cA
    cW
    cascl
    cfv
    #
    vx
    cK
    vx
    cv
    #
    c.1
    c.x
    co
    #
    cmpt
    #
    asclfval.a
    cW
    cvv
    wcel
    #
    @0
    @3
    wceq
    vw
    cW
    vx
    vw
    cv
    #
    csca
    cfv
    #
    cbs
    cfv
    #
    @1
    @5
    cur
    cfv
    #
    @5
    cvsca
    cfv
    #
    co
    #
    cmpt
    @3
    cvv
    cascl
    @5
    cW
    wceq
    #
    vx
    @7
    @10
    cK
    @2
    @11
    @7
    cF
    cbs
    cfv
    #
    cK
    @11
    @6
    cF
    cbs
    @11
    @6
    cW
    csca
    cfv
    #
    cF
    @5
    cW
    csca
    fveq2
    asclfval.f
    syl6eqr
    fveq2d
    asclfval.k
    syl6eqr
    @11
    @1
    @1
    @8
    c.1
    @9
    c.x
    @11
    @9
    cW
    cvsca
    cfv
    c.x
    @5
    cW
    cvsca
    fveq2
    asclfval.s
    syl6eqr
    @11
    @1
    eqidd
    @11
    @8
    cW
    cur
    cfv
    c.1
    @5
    cW
    cur
    fveq2
    asclfval.o
    syl6eqr
    oveq123d
    mpteq12dv
    vx
    vw
    df-ascl
    vx
    cK
    @2
    cK
    @13
    cbs
    cfv
    #
    cvv
    cK
    @12
    @14
    asclfval.k
    cF
    @13
    cbs
    asclfval.f
    fveq2i
    eqtri
    @13
    cbs
    fvex
    eqeltri
    mptex
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
    cW
    cascl
    fvprc
    vx
    @2
    mpt0
    syl6eqr
    @15
    vx
    cK
    c0
    @2
    @15
    cK
    @12
    c0
    asclfval.k
    @15
    @12
    c0
    cbs
    cfv
    c0
    @15
    cF
    c0
    cbs
    @15
    cF
    @13
    c0
    asclfval.f
    cW
    csca
    fvprc
    syl5eq
    fveq2d
    base0
    syl6eqr
    syl5eq
    mpteq1d
    eqtr4d
    pm2.61i
    eqtri
end

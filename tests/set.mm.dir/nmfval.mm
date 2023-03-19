include "cnm.mm"
include "cfv.mm"
include "cv.mm"
include "co.mm"
include "cmpt.mm"
include "cvv.mm"
include "wcel.mm"
include "wceq.mm"
include "cbs.mm"
include "c0g.mm"
include "cds.mm"
include "fveq2.mm"
include "syl6eqr.mm"
include "eqidd.mm"
include "oveq123d.mm"
include "mpteq12dv.mm"
include "df-nm.mm"
include "crn.mm"
include "c0.mm"
include "csn.mm"
include "cun.mm"
include "wf.mm"
include "eqid.mm"
include "cop.mm"
include "df-ov.mm"
include "fvrn0.mm"
include "eqeltri.mm"
include "a1i.mm"
include "fmpti.mm"
include "fvex.mm"
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

theorem nmfval
  let vx: setvar x
  let cD: class D
  let cN: class N
  let cW: class W
  let cX: class X
  let c.0: class .0.
  let cA: class A
  let vw: setvar w
  assume nmfval.n: |- N = ( norm ` W )
  assume nmfval.x: |- X = ( Base ` W )
  assume nmfval.z: |- .0. = ( 0g ` W )
  assume nmfval.d: |- D = ( dist ` W )

  disjoint D x
  disjoint W x
  disjoint X x
  disjoint .0. x
  disjoint A x
  disjoint w x
  disjoint D w
  disjoint W w
  disjoint X w
  disjoint .0. w
  assert |- N = ( x e. X |-> ( x D .0. ) )

  proof
    cN
    cW
    cnm
    cfv
    #
    vx
    cX
    vx
    cv
    #
    c.0
    cD
    co
    #
    cmpt
    #
    nmfval.n
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
    cbs
    cfv
    #
    @1
    @5
    c0g
    cfv
    #
    @5
    cds
    cfv
    #
    co
    #
    cmpt
    @3
    cvv
    cnm
    @5
    cW
    wceq
    #
    vx
    @6
    @9
    cX
    @2
    @10
    @6
    cW
    cbs
    cfv
    #
    cX
    @5
    cW
    cbs
    fveq2
    nmfval.x
    syl6eqr
    @10
    @1
    @1
    @7
    c.0
    @8
    cD
    @10
    @8
    cW
    cds
    cfv
    #
    cD
    @5
    cW
    cds
    fveq2
    nmfval.d
    syl6eqr
    @10
    @1
    eqidd
    @10
    @7
    cW
    c0g
    cfv
    c.0
    @5
    cW
    c0g
    fveq2
    nmfval.z
    syl6eqr
    oveq123d
    mpteq12dv
    vx
    vw
    df-nm
    cX
    cD
    crn
    #
    c0
    csn
    #
    cun
    #
    @3
    wf
    cX
    cvv
    wcel
    @15
    cvv
    wcel
    @3
    cvv
    wcel
    vx
    cX
    @15
    @2
    @3
    @3
    eqid
    @2
    @15
    wcel
    @1
    cX
    wcel
    @2
    @1
    c.0
    cop
    #
    cD
    cfv
    @15
    @1
    c.0
    cD
    df-ov
    cD
    @16
    fvrn0
    eqeltri
    a1i
    fmpti
    cX
    @11
    cvv
    nmfval.x
    cW
    cbs
    fvex
    eqeltri
    @13
    @14
    cD
    cD
    @12
    cvv
    nmfval.d
    cW
    cds
    fvex
    eqeltri
    rnex
    p0ex
    unex
    cX
    @15
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
    @17
    @0
    c0
    @18
    cW
    cnm
    fvprc
    vx
    @2
    mpt0
    syl6eqr
    @17
    vx
    cX
    c0
    @2
    @17
    cX
    @11
    c0
    nmfval.x
    cW
    cbs
    fvprc
    syl5eq
    mpteq1d
    eqtr4d
    pm2.61i
    eqtri
end

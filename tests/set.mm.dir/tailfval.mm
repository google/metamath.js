include "cdir.mm"
include "wcel.mm"
include "ctail.mm"
include "cfv.mm"
include "cuni.mm"
include "cv.mm"
include "csn.mm"
include "cima.mm"
include "cmpt.mm"
include "cvv.mm"
include "wceq.mm"
include "uniexg.mm"
include "mptexg.mm"
include "3syl.mm"
include "unieq.mm"
include "unieqd.mm"
include "imaeq1.mm"
include "mpteq12dv.mm"
include "df-tail.mm"
include "fvmptg.mm"
include "mpdan.mm"
include "cdm.mm"
include "dirdm.mm"
include "syl5req.mm"
include "mpteq1d.mm"
include "eqtrd.mm"

theorem tailfval
  let vx: setvar x
  let cD: class D
  let cX: class X
  let vd: setvar d
  let cA: class A
  assume tailfval.1: |- X = dom D

  disjoint D x
  disjoint X x
  disjoint d x
  disjoint D d
  disjoint A x
  assert |- ( D e. DirRel -> ( tail ` D ) = ( x e. X |-> ( D " { x } ) ) )

  proof
    cD
    cdir
    wcel
    #
    cD
    ctail
    cfv
    #
    vx
    cD
    cuni
    #
    cuni
    #
    cD
    vx
    cv
    csn
    #
    cima
    #
    cmpt
    #
    vx
    cX
    @5
    cmpt
    @0
    @6
    cvv
    wcel
    #
    @1
    @6
    wceq
    @0
    @2
    cvv
    wcel
    @3
    cvv
    wcel
    @7
    cD
    cdir
    uniexg
    @2
    cvv
    uniexg
    vx
    @3
    @5
    cvv
    mptexg
    3syl
    vd
    cD
    vx
    vd
    cv
    #
    cuni
    #
    cuni
    #
    @8
    @4
    cima
    #
    cmpt
    @6
    cdir
    cvv
    ctail
    @8
    cD
    wceq
    #
    vx
    @10
    @11
    @3
    @5
    @12
    @9
    @2
    @8
    cD
    unieq
    unieqd
    @8
    cD
    @4
    imaeq1
    mpteq12dv
    vx
    vd
    df-tail
    fvmptg
    mpdan
    @0
    vx
    @3
    cX
    @5
    @0
    cX
    cD
    cdm
    @3
    tailfval.1
    cD
    dirdm
    syl5req
    mpteq1d
    eqtrd
end

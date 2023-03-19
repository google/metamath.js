include "c2o.mm"
include "cmap.mm"
include "co.mm"
include "wcel.mm"
include "ccnv.mm"
include "c1o.mm"
include "csn.mm"
include "cima.mm"
include "cvv.mm"
include "cfv.mm"
include "wceq.mm"
include "cnvexg.mm"
include "imaexg.mm"
include "syl.mm"
include "cv.mm"
include "cnveq.mm"
include "imaeq1d.mm"
include "fvmptg.mm"
include "mpdan.mm"

theorem pw2f1o2val
  let vx: setvar x
  let cA: class A
  let cF: class F
  let cX: class X
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let cY: class Y
  let cV: class V
  assume pw2f1o2.f: |- F = ( x e. ( 2o ^m A ) |-> ( `' x " { 1o } ) )

  disjoint A x
  disjoint X x
  disjoint A y
  disjoint A z
  disjoint A w
  disjoint x y
  disjoint x z
  disjoint w x
  disjoint y z
  disjoint w y
  disjoint w z
  disjoint X y
  disjoint Y x
  disjoint Y y
  disjoint V x
  disjoint V y
  assert |- ( X e. ( 2o ^m A ) -> ( F ` X ) = ( `' X " { 1o } ) )

  proof
    cX
    c2o
    cA
    cmap
    co
    #
    wcel
    #
    cX
    ccnv
    #
    c1o
    csn
    #
    cima
    #
    cvv
    wcel
    #
    cX
    cF
    cfv
    @4
    wceq
    @1
    @2
    cvv
    wcel
    @5
    cX
    @0
    cnvexg
    @2
    @3
    cvv
    imaexg
    syl
    vx
    cX
    vx
    cv
    #
    ccnv
    #
    @3
    cima
    @4
    @0
    cvv
    cF
    @6
    cX
    wceq
    @7
    @2
    @3
    @6
    cX
    cnveq
    imaeq1d
    pw2f1o2.f
    fvmptg
    mpdan
end

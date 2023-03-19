include "wcel.mm"
include "cfv.mm"
include "cv.mm"
include "ccnv.mm"
include "csn.mm"
include "cima.mm"
include "cmpt.mm"
include "lkrfval.mm"
include "fveq1d.mm"
include "cvv.mm"
include "wceq.mm"
include "cnvexg.mm"
include "imaexg.mm"
include "syl.mm"
include "cnveq.mm"
include "imaeq1d.mm"
include "eqid.mm"
include "fvmptg.mm"
include "mpdan.mm"
include "sylan9eq.mm"

theorem lkrval
  let cD: class D
  let cF: class F
  let cG: class G
  let cK: class K
  let cW: class W
  let cX: class X
  let c.0: class .0.
  let vf: setvar f
  let vw: setvar w
  assume lkrfval.d: |- D = ( Scalar ` W )
  assume lkrfval.o: |- .0. = ( 0g ` D )
  assume lkrfval.f: |- F = ( LFnl ` W )
  assume lkrfval.k: |- K = ( LKer ` W )


  assert |- ( ( W e. X /\ G e. F ) -> ( K ` G ) = ( `' G " { .0. } ) )

  proof
    cW
    cX
    wcel
    #
    cG
    cF
    wcel
    #
    cG
    cK
    cfv
    cG
    vf
    cF
    vf
    cv
    #
    ccnv
    #
    c.0
    csn
    #
    cima
    #
    cmpt
    #
    cfv
    #
    cG
    ccnv
    #
    @4
    cima
    #
    @0
    cG
    cK
    @6
    cD
    vf
    cF
    cK
    cW
    cX
    c.0
    lkrfval.d
    lkrfval.o
    lkrfval.f
    lkrfval.k
    lkrfval
    fveq1d
    @1
    @9
    cvv
    wcel
    #
    @7
    @9
    wceq
    @1
    @8
    cvv
    wcel
    @10
    cG
    cF
    cnvexg
    @8
    @4
    cvv
    imaexg
    syl
    vf
    cG
    @5
    @9
    cF
    cvv
    @6
    @2
    cG
    wceq
    @3
    @8
    @4
    @2
    cG
    cnveq
    imaeq1d
    @6
    eqid
    fvmptg
    mpdan
    sylan9eq
end

include "cdir.mm"
include "wcel.mm"
include "wa.mm"
include "ctail.mm"
include "cfv.mm"
include "cv.mm"
include "csn.mm"
include "cima.mm"
include "cmpt.mm"
include "wceq.mm"
include "tailfval.mm"
include "fveq1d.mm"
include "adantr.mm"
include "cvv.mm"
include "id.mm"
include "imaexg.mm"
include "sneq.mm"
include "imaeq2d.mm"
include "eqid.mm"
include "fvmptg.mm"
include "syl2anr.mm"
include "eqtrd.mm"

theorem tailval
  let cA: class A
  let cD: class D
  let cX: class X
  let vd: setvar d
  let vx: setvar x
  assume tailfval.1: |- X = dom D


  assert |- ( ( D e. DirRel /\ A e. X ) -> ( ( tail ` D ) ` A ) = ( D " { A } ) )

  proof
    cD
    cdir
    wcel
    #
    cA
    cX
    wcel
    #
    wa
    cA
    cD
    ctail
    cfv
    #
    cfv
    #
    cA
    vx
    cX
    cD
    vx
    cv
    #
    csn
    #
    cima
    #
    cmpt
    #
    cfv
    #
    cD
    cA
    csn
    #
    cima
    #
    @0
    @3
    @8
    wceq
    @1
    @0
    cA
    @2
    @7
    vx
    cD
    cX
    tailfval.1
    tailfval
    fveq1d
    adantr
    @1
    @1
    @10
    cvv
    wcel
    @8
    @10
    wceq
    @0
    @1
    id
    cD
    @9
    cdir
    imaexg
    vx
    cA
    @6
    @10
    cX
    cvv
    @7
    @4
    cA
    wceq
    @5
    @9
    cD
    @4
    cA
    sneq
    imaeq2d
    @7
    eqid
    fvmptg
    syl2anr
    eqtrd
end

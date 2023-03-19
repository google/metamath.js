include "wfun.mm"
include "wcel.mm"
include "wa.mm"
include "cres.mm"
include "cdm.mm"
include "cv.mm"
include "cfv.mm"
include "cop.mm"
include "cmpt.mm"
include "cima.mm"
include "cvv.mm"
include "crn.mm"
include "wfn.mm"
include "wceq.mm"
include "funres.mm"
include "adantr.mm"
include "funfn.mm"
include "sylib.mm"
include "dffn5.mm"
include "fvex.mm"
include "fnasrn.mm"
include "syl6eq.mm"
include "opex.mm"
include "eqid.mm"
include "dmmpti.mm"
include "imaeq2i.mm"
include "imadmrn.mm"
include "eqtr3i.mm"
include "syl6eqr.mm"
include "funmpt.mm"
include "dmresexg.mm"
include "adantl.mm"
include "funimaexg.mm"
include "sylancr.mm"
include "eqeltrd.mm"

theorem resfunexg
  let cA: class A
  let cB: class B
  let cC: class C
  let vx: setvar x


  assert |- ( ( Fun A /\ B e. C ) -> ( A |` B ) e. _V )

  proof
    cA
    wfun
    #
    cB
    cC
    wcel
    #
    wa
    #
    cA
    cB
    cres
    #
    vx
    @3
    cdm
    #
    vx
    cv
    #
    @5
    @3
    cfv
    #
    cop
    #
    cmpt
    #
    @4
    cima
    #
    cvv
    @2
    @3
    @8
    crn
    #
    @9
    @2
    @3
    vx
    @4
    @6
    cmpt
    #
    @10
    @2
    @3
    @4
    wfn
    #
    @3
    @11
    wceq
    @2
    @3
    wfun
    #
    @12
    @0
    @13
    @1
    cB
    cA
    funres
    adantr
    @3
    funfn
    sylib
    vx
    @4
    @3
    dffn5
    sylib
    vx
    @4
    @6
    @5
    @3
    fvex
    fnasrn
    syl6eq
    @8
    @8
    cdm
    #
    cima
    @9
    @10
    @14
    @4
    @8
    vx
    @4
    @7
    @8
    @5
    @6
    opex
    @8
    eqid
    dmmpti
    imaeq2i
    @8
    imadmrn
    eqtr3i
    syl6eqr
    @2
    @8
    wfun
    @4
    cvv
    wcel
    #
    @9
    cvv
    wcel
    vx
    @4
    @7
    funmpt
    @1
    @15
    @0
    cA
    cB
    cC
    dmresexg
    adantl
    @8
    @4
    cvv
    funimaexg
    sylancr
    eqeltrd
end

include "csn.mm"
include "wfn.mm"
include "cfv.mm"
include "cop.mm"
include "wceq.mm"
include "cv.mm"
include "wcel.mm"
include "fnsnr.mm"
include "wfun.mm"
include "cdm.mm"
include "wa.mm"
include "df-fn.mm"
include "snid.mm"
include "eleq2.mm"
include "mpbiri.mm"
include "anim2i.mm"
include "sylbi.mm"
include "funfvop.mm"
include "syl.mm"
include "eleq1.mm"
include "syl5ibrcom.mm"
include "impbid.mm"
include "velsn.mm"
include "syl6bbr.mm"
include "eqrdv.mm"
include "fvex.mm"
include "fnsn.mm"
include "fneq1.mm"
include "impbii.mm"

theorem fnsnb
  let cA: class A
  let cF: class F
  let vx: setvar x
  assume fnsnb.1: |- A e. _V


  assert |- ( F Fn { A } <-> F = { <. A , ( F ` A ) >. } )

  proof
    cF
    cA
    csn
    #
    wfn
    #
    cF
    cA
    cA
    cF
    cfv
    #
    cop
    #
    csn
    #
    wceq
    #
    @1
    vx
    cF
    @4
    @1
    vx
    cv
    #
    cF
    wcel
    #
    @6
    @3
    wceq
    #
    @6
    @4
    wcel
    @1
    @7
    @8
    cA
    @6
    cF
    fnsnr
    @1
    @7
    @8
    @3
    cF
    wcel
    #
    @1
    cF
    wfun
    #
    cA
    cF
    cdm
    #
    wcel
    #
    wa
    #
    @9
    @1
    @10
    @11
    @0
    wceq
    #
    wa
    @13
    cF
    @0
    df-fn
    @14
    @12
    @10
    @14
    @12
    cA
    @0
    wcel
    cA
    fnsnb.1
    snid
    @11
    @0
    cA
    eleq2
    mpbiri
    anim2i
    sylbi
    cA
    cF
    funfvop
    syl
    @6
    @3
    cF
    eleq1
    syl5ibrcom
    impbid
    vx
    @3
    velsn
    syl6bbr
    eqrdv
    @5
    @1
    @4
    @0
    wfn
    cA
    @2
    fnsnb.1
    cA
    cF
    fvex
    fnsn
    @0
    cF
    @4
    fneq1
    mpbiri
    impbii
end

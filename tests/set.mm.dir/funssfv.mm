include "wfun.mm"
include "wss.mm"
include "cdm.mm"
include "wcel.mm"
include "cfv.mm"
include "wceq.mm"
include "wa.mm"
include "cres.mm"
include "fvres.mm"
include "eqcomd.mm"
include "funssres.mm"
include "fveq1d.mm"
include "sylan9eqr.mm"
include "3impa.mm"

theorem funssfv
  let cA: class A
  let cF: class F
  let cG: class G


  assert |- ( ( Fun F /\ G C_ F /\ A e. dom G ) -> ( F ` A ) = ( G ` A ) )

  proof
    cF
    wfun
    #
    cG
    cF
    wss
    #
    cA
    cG
    cdm
    #
    wcel
    #
    cA
    cF
    cfv
    #
    cA
    cG
    cfv
    #
    wceq
    @3
    @0
    @1
    wa
    #
    @4
    cA
    cF
    @2
    cres
    #
    cfv
    #
    @5
    @3
    @8
    @4
    cA
    @2
    cF
    fvres
    eqcomd
    @6
    cA
    @7
    cG
    cF
    cG
    funssres
    fveq1d
    sylan9eqr
    3impa
end

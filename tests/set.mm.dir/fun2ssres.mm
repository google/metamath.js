include "wfun.mm"
include "wss.mm"
include "cdm.mm"
include "cres.mm"
include "wceq.mm"
include "wa.mm"
include "resabs1.mm"
include "eqcomd.mm"
include "funssres.mm"
include "reseq1d.mm"
include "sylan9eqr.mm"
include "3impa.mm"

theorem fun2ssres
  let cA: class A
  let cF: class F
  let cG: class G


  assert |- ( ( Fun F /\ G C_ F /\ A C_ dom G ) -> ( F |` A ) = ( G |` A ) )

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
    wss
    #
    cF
    cA
    cres
    #
    cG
    cA
    cres
    #
    wceq
    @3
    @0
    @1
    wa
    #
    @4
    cF
    @2
    cres
    #
    cA
    cres
    #
    @5
    @3
    @8
    @4
    cF
    cA
    @2
    resabs1
    eqcomd
    @6
    @7
    cG
    cA
    cF
    cG
    funssres
    reseq1d
    sylan9eqr
    3impa
end

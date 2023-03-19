include "ccn.mm"
include "co.mm"
include "wcel.mm"
include "ccnv.mm"
include "cv.mm"
include "cima.mm"
include "wral.mm"
include "cuni.mm"
include "wf.mm"
include "ctop.mm"
include "wa.mm"
include "eqid.mm"
include "iscn2.mm"
include "simprbi.mm"
include "simprd.mm"
include "wceq.mm"
include "imaeq2.mm"
include "eleq1d.mm"
include "rspccva.mm"
include "sylan.mm"

theorem cnima
  let cA: class A
  let cF: class F
  let cJ: class J
  let cK: class K
  let vx: setvar x


  assert |- ( ( F e. ( J Cn K ) /\ A e. K ) -> ( `' F " A ) e. J )

  proof
    cF
    cJ
    cK
    ccn
    co
    wcel
    #
    cF
    ccnv
    #
    vx
    cv
    #
    cima
    #
    cJ
    wcel
    #
    vx
    cK
    wral
    #
    cA
    cK
    wcel
    @1
    cA
    cima
    #
    cJ
    wcel
    #
    @0
    cJ
    cuni
    #
    cK
    cuni
    #
    cF
    wf
    #
    @5
    @0
    cJ
    ctop
    wcel
    cK
    ctop
    wcel
    wa
    @10
    @5
    wa
    vx
    cF
    cJ
    cK
    @8
    @9
    @8
    eqid
    @9
    eqid
    iscn2
    simprbi
    simprd
    @4
    @7
    vx
    cA
    cK
    @2
    cA
    wceq
    @3
    @6
    cJ
    @2
    cA
    @1
    imaeq2
    eleq1d
    rspccva
    sylan
end

include "wf.mm"
include "cin.mm"
include "c0.mm"
include "wceq.mm"
include "w3a.mm"
include "cdm.mm"
include "crn.mm"
include "ccom.mm"
include "wss.mm"
include "frn.mm"
include "3ad2ant2.mm"
include "sslin.mm"
include "syl.mm"
include "fdm.mm"
include "3ad2ant1.mm"
include "ineq1d.mm"
include "simp3.mm"
include "eqtrd.mm"
include "sseqtrd.mm"
include "ss0.mm"
include "coeq0.mm"
include "sylibr.mm"

theorem coeq0i
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cE: class E
  let cF: class F


  assert |- ( ( A : C --> D /\ B : E --> F /\ ( C i^i F ) = (/) ) -> ( A o. B ) = (/) )

  proof
    cC
    cD
    cA
    wf
    #
    cE
    cF
    cB
    wf
    #
    cC
    cF
    cin
    #
    c0
    wceq
    #
    w3a
    #
    cA
    cdm
    #
    cB
    crn
    #
    cin
    #
    c0
    wceq
    #
    cA
    cB
    ccom
    c0
    wceq
    @4
    @7
    c0
    wss
    @8
    @4
    @7
    @5
    cF
    cin
    #
    c0
    @4
    @6
    cF
    wss
    #
    @7
    @9
    wss
    @1
    @0
    @10
    @3
    cE
    cF
    cB
    frn
    3ad2ant2
    @6
    cF
    @5
    sslin
    syl
    @4
    @9
    @2
    c0
    @4
    @5
    cC
    cF
    @0
    @1
    @5
    cC
    wceq
    @3
    cC
    cD
    cA
    fdm
    3ad2ant1
    ineq1d
    @0
    @1
    @3
    simp3
    eqtrd
    sseqtrd
    @7
    ss0
    syl
    cA
    cB
    coeq0
    sylibr
end

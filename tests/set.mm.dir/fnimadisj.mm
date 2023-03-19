include "wfn.mm"
include "cin.mm"
include "c0.mm"
include "wceq.mm"
include "wa.mm"
include "cdm.mm"
include "cima.mm"
include "fndm.mm"
include "ineq1d.mm"
include "eqeq1d.mm"
include "biimpar.mm"
include "imadisj.mm"
include "sylibr.mm"

theorem fnimadisj
  let cA: class A
  let cC: class C
  let cF: class F


  assert |- ( ( F Fn A /\ ( A i^i C ) = (/) ) -> ( F " C ) = (/) )

  proof
    cF
    cA
    wfn
    #
    cA
    cC
    cin
    #
    c0
    wceq
    #
    wa
    cF
    cdm
    #
    cC
    cin
    #
    c0
    wceq
    #
    cF
    cC
    cima
    c0
    wceq
    @0
    @5
    @2
    @0
    @4
    @1
    c0
    @0
    @3
    cA
    cC
    cA
    cF
    fndm
    ineq1d
    eqeq1d
    biimpar
    cF
    cC
    imadisj
    sylibr
end

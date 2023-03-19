include "wfn.mm"
include "crn.mm"
include "cin.mm"
include "wss.mm"
include "wa.mm"
include "wf.mm"
include "ssin.mm"
include "anbi2i.mm"
include "anandi.mm"
include "bitr3i.mm"
include "df-f.mm"
include "anbi12i.mm"
include "3bitr4i.mm"

theorem fin
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F


  assert |- ( F : A --> ( B i^i C ) <-> ( F : A --> B /\ F : A --> C ) )

  proof
    cF
    cA
    wfn
    #
    cF
    crn
    #
    cB
    cC
    cin
    #
    wss
    #
    wa
    #
    @0
    @1
    cB
    wss
    #
    wa
    #
    @0
    @1
    cC
    wss
    #
    wa
    #
    wa
    #
    cA
    @2
    cF
    wf
    cA
    cB
    cF
    wf
    #
    cA
    cC
    cF
    wf
    #
    wa
    @4
    @0
    @5
    @7
    wa
    #
    wa
    @9
    @12
    @3
    @0
    @1
    cB
    cC
    ssin
    anbi2i
    @0
    @5
    @7
    anandi
    bitr3i
    cA
    @2
    cF
    df-f
    @10
    @6
    @11
    @8
    cA
    cB
    cF
    df-f
    cA
    cC
    cF
    df-f
    anbi12i
    3bitr4i
end

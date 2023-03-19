include "wf1.mm"
include "wss.mm"
include "wa.mm"
include "cres.mm"
include "crn.mm"
include "wf1o.mm"
include "cima.mm"
include "f1ssres.mm"
include "f1f1orn.mm"
include "syl.mm"
include "wceq.mm"
include "wb.mm"
include "df-ima.mm"
include "f1oeq3.mm"
include "ax-mp.mm"
include "sylibr.mm"

theorem f1ores
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F


  assert |- ( ( F : A -1-1-> B /\ C C_ A ) -> ( F |` C ) : C -1-1-onto-> ( F " C ) )

  proof
    cA
    cB
    cF
    wf1
    cC
    cA
    wss
    wa
    #
    cC
    cF
    cC
    cres
    #
    crn
    #
    @1
    wf1o
    #
    cC
    cF
    cC
    cima
    #
    @1
    wf1o
    #
    @0
    cC
    cB
    @1
    wf1
    @3
    cA
    cB
    cC
    cF
    f1ssres
    cC
    cB
    @1
    f1f1orn
    syl
    @4
    @2
    wceq
    @5
    @3
    wb
    cF
    cC
    df-ima
    @4
    @2
    cC
    @1
    f1oeq3
    ax-mp
    sylibr
end

include "wf1o.mm"
include "wa.mm"
include "ccom.mm"
include "wf1.mm"
include "wfo.mm"
include "df-f1o.mm"
include "f1co.mm"
include "foco.mm"
include "anim12i.mm"
include "an4s.mm"
include "syl2anb.mm"
include "sylibr.mm"

theorem f1oco
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F
  let cG: class G


  assert |- ( ( F : B -1-1-onto-> C /\ G : A -1-1-onto-> B ) -> ( F o. G ) : A -1-1-onto-> C )

  proof
    cB
    cC
    cF
    wf1o
    #
    cA
    cB
    cG
    wf1o
    #
    wa
    cA
    cC
    cF
    cG
    ccom
    #
    wf1
    #
    cA
    cC
    @2
    wfo
    #
    wa
    #
    cA
    cC
    @2
    wf1o
    @0
    cB
    cC
    cF
    wf1
    #
    cB
    cC
    cF
    wfo
    #
    wa
    cA
    cB
    cG
    wf1
    #
    cA
    cB
    cG
    wfo
    #
    wa
    @5
    @1
    cB
    cC
    cF
    df-f1o
    cA
    cB
    cG
    df-f1o
    @6
    @8
    @7
    @9
    @5
    @6
    @8
    wa
    @3
    @7
    @9
    wa
    @4
    cA
    cB
    cC
    cF
    cG
    f1co
    cA
    cB
    cC
    cF
    cG
    foco
    anim12i
    an4s
    syl2anb
    cA
    cC
    @2
    df-f1o
    sylibr
end

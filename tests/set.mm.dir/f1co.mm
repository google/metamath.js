include "wf1.mm"
include "wa.mm"
include "ccom.mm"
include "wf.mm"
include "ccnv.mm"
include "wfun.mm"
include "df-f1.mm"
include "fco.mm"
include "funco.mm"
include "cnvco.mm"
include "funeqi.mm"
include "sylibr.mm"
include "ancoms.mm"
include "anim12i.mm"
include "an4s.mm"
include "syl2anb.mm"

theorem f1co
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F
  let cG: class G


  assert |- ( ( F : B -1-1-> C /\ G : A -1-1-> B ) -> ( F o. G ) : A -1-1-> C )

  proof
    cB
    cC
    cF
    wf1
    #
    cA
    cB
    cG
    wf1
    #
    wa
    cA
    cC
    cF
    cG
    ccom
    #
    wf
    #
    @2
    ccnv
    #
    wfun
    #
    wa
    #
    cA
    cC
    @2
    wf1
    @0
    cB
    cC
    cF
    wf
    #
    cF
    ccnv
    #
    wfun
    #
    wa
    cA
    cB
    cG
    wf
    #
    cG
    ccnv
    #
    wfun
    #
    wa
    @6
    @1
    cB
    cC
    cF
    df-f1
    cA
    cB
    cG
    df-f1
    @7
    @10
    @9
    @12
    @6
    @7
    @10
    wa
    @3
    @9
    @12
    wa
    @5
    cA
    cB
    cC
    cF
    cG
    fco
    @12
    @9
    @5
    @12
    @9
    wa
    @11
    @8
    ccom
    #
    wfun
    @5
    @11
    @8
    funco
    @4
    @13
    cF
    cG
    cnvco
    funeqi
    sylibr
    ancoms
    anim12i
    an4s
    syl2anb
    cA
    cC
    @2
    df-f1
    sylibr
end

include "wfo.mm"
include "wa.mm"
include "cin.mm"
include "c0.mm"
include "wceq.mm"
include "cun.mm"
include "wfn.mm"
include "crn.mm"
include "fofn.mm"
include "anim12i.mm"
include "fnun.mm"
include "sylan.mm"
include "rnun.mm"
include "forn.mm"
include "ad2antrr.mm"
include "ad2antlr.mm"
include "uneq12d.mm"
include "syl5eq.mm"
include "df-fo.mm"
include "sylanbrc.mm"

theorem foun
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cF: class F
  let cG: class G


  assert |- ( ( ( F : A -onto-> B /\ G : C -onto-> D ) /\ ( A i^i C ) = (/) ) -> ( F u. G ) : ( A u. C ) -onto-> ( B u. D ) )

  proof
    cA
    cB
    cF
    wfo
    #
    cC
    cD
    cG
    wfo
    #
    wa
    #
    cA
    cC
    cin
    c0
    wceq
    #
    wa
    #
    cF
    cG
    cun
    #
    cA
    cC
    cun
    #
    wfn
    #
    @5
    crn
    #
    cB
    cD
    cun
    #
    wceq
    @6
    @9
    @5
    wfo
    @2
    cF
    cA
    wfn
    #
    cG
    cC
    wfn
    #
    wa
    @3
    @7
    @0
    @10
    @1
    @11
    cA
    cB
    cF
    fofn
    cC
    cD
    cG
    fofn
    anim12i
    cA
    cC
    cF
    cG
    fnun
    sylan
    @4
    @8
    cF
    crn
    #
    cG
    crn
    #
    cun
    @9
    cF
    cG
    rnun
    @4
    @12
    cB
    @13
    cD
    @0
    @12
    cB
    wceq
    @1
    @3
    cA
    cB
    cF
    forn
    ad2antrr
    @1
    @13
    cD
    wceq
    @0
    @3
    cC
    cD
    cG
    forn
    ad2antlr
    uneq12d
    syl5eq
    @6
    @9
    @5
    df-fo
    sylanbrc
end

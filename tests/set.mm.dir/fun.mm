include "cin.mm"
include "c0.mm"
include "wceq.mm"
include "wf.mm"
include "wa.mm"
include "cun.mm"
include "wfn.mm"
include "crn.mm"
include "wss.mm"
include "fnun.mm"
include "expcom.mm"
include "wi.mm"
include "rnun.mm"
include "unss12.mm"
include "syl5eqss.mm"
include "a1i.mm"
include "anim12d.mm"
include "df-f.mm"
include "anbi12i.mm"
include "an4.mm"
include "bitri.mm"
include "3imtr4g.mm"
include "impcom.mm"

theorem fun
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cF: class F
  let cG: class G


  assert |- ( ( ( F : A --> C /\ G : B --> D ) /\ ( A i^i B ) = (/) ) -> ( F u. G ) : ( A u. B ) --> ( C u. D ) )

  proof
    cA
    cB
    cin
    c0
    wceq
    #
    cA
    cC
    cF
    wf
    #
    cB
    cD
    cG
    wf
    #
    wa
    #
    cA
    cB
    cun
    #
    cC
    cD
    cun
    #
    cF
    cG
    cun
    #
    wf
    #
    @0
    cF
    cA
    wfn
    #
    cG
    cB
    wfn
    #
    wa
    #
    cF
    crn
    #
    cC
    wss
    #
    cG
    crn
    #
    cD
    wss
    #
    wa
    #
    wa
    #
    @6
    @4
    wfn
    #
    @6
    crn
    #
    @5
    wss
    #
    wa
    @3
    @7
    @0
    @10
    @17
    @15
    @19
    @10
    @0
    @17
    cA
    cB
    cF
    cG
    fnun
    expcom
    @15
    @19
    wi
    @0
    @15
    @18
    @11
    @13
    cun
    @5
    cF
    cG
    rnun
    @11
    cC
    @13
    cD
    unss12
    syl5eqss
    a1i
    anim12d
    @3
    @8
    @12
    wa
    #
    @9
    @14
    wa
    #
    wa
    @16
    @1
    @20
    @2
    @21
    cA
    cC
    cF
    df-f
    cB
    cD
    cG
    df-f
    anbi12i
    @8
    @12
    @9
    @14
    an4
    bitri
    @4
    @5
    @6
    df-f
    3imtr4g
    impcom
end

include "wf1.mm"
include "wa.mm"
include "wcel.mm"
include "cfv.mm"
include "wceq.mm"
include "ccom.mm"
include "wb.mm"
include "wi.mm"
include "wf.mm"
include "f1f.mm"
include "fvco3.mm"
include "adantrr.mm"
include "adantrl.mm"
include "eqeq12d.mm"
include "ex.mm"
include "syl.mm"
include "adantl.mm"
include "imp.mm"
include "f1co.mm"
include "f1veqaeq.mm"
include "sylan.mm"
include "sylbird.mm"

theorem f1cofveqaeqALT
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F
  let cG: class G
  let cX: class X
  let cY: class Y


  assert |- ( ( ( F : B -1-1-> C /\ G : A -1-1-> B ) /\ ( X e. A /\ Y e. A ) ) -> ( ( F ` ( G ` X ) ) = ( F ` ( G ` Y ) ) -> X = Y ) )

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
    #
    cX
    cA
    wcel
    #
    cY
    cA
    wcel
    #
    wa
    #
    wa
    cX
    cG
    cfv
    cF
    cfv
    #
    cY
    cG
    cfv
    cF
    cfv
    #
    wceq
    #
    cX
    cF
    cG
    ccom
    #
    cfv
    #
    cY
    @9
    cfv
    #
    wceq
    #
    cX
    cY
    wceq
    #
    @2
    @5
    @12
    @8
    wb
    #
    @1
    @5
    @14
    wi
    #
    @0
    @1
    cA
    cB
    cG
    wf
    #
    @15
    cA
    cB
    cG
    f1f
    @16
    @5
    @14
    @16
    @5
    wa
    @10
    @6
    @11
    @7
    @16
    @3
    @10
    @6
    wceq
    @4
    cA
    cB
    cX
    cF
    cG
    fvco3
    adantrr
    @16
    @4
    @11
    @7
    wceq
    @3
    cA
    cB
    cY
    cF
    cG
    fvco3
    adantrl
    eqeq12d
    ex
    syl
    adantl
    imp
    @2
    cA
    cC
    @9
    wf1
    @5
    @12
    @13
    wi
    cA
    cB
    cC
    cF
    cG
    f1co
    cA
    cC
    cX
    cY
    @9
    f1veqaeq
    sylan
    sylbird
end

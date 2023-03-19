include "wf.mm"
include "wa.mm"
include "cin.mm"
include "c0.mm"
include "wceq.mm"
include "cun.mm"
include "fun.mm"
include "wb.mm"
include "unidm.mm"
include "feq3.mm"
include "ax-mp.mm"
include "sylib.mm"

theorem fun2
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F
  let cG: class G


  assert |- ( ( ( F : A --> C /\ G : B --> C ) /\ ( A i^i B ) = (/) ) -> ( F u. G ) : ( A u. B ) --> C )

  proof
    cA
    cC
    cF
    wf
    cB
    cC
    cG
    wf
    wa
    cA
    cB
    cin
    c0
    wceq
    wa
    cA
    cB
    cun
    #
    cC
    cC
    cun
    #
    cF
    cG
    cun
    #
    wf
    #
    @0
    cC
    @2
    wf
    #
    cA
    cB
    cC
    cC
    cF
    cG
    fun
    @1
    cC
    wceq
    @3
    @4
    wb
    cC
    unidm
    @1
    cC
    @0
    @2
    feq3
    ax-mp
    sylib
end

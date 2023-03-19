include "wf1.mm"
include "wa.mm"
include "wcel.mm"
include "cfv.mm"
include "wceq.mm"
include "wi.mm"
include "simpl.mm"
include "wf.mm"
include "f1f.mm"
include "ffvelrn.mm"
include "ex.mm"
include "anim12d.mm"
include "syl.mm"
include "adantl.mm"
include "imp.mm"
include "f1veqaeq.mm"
include "syl2an2r.mm"
include "adantll.mm"
include "syld.mm"

theorem f1cofveqaeq
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
    #
    cF
    cfv
    cY
    cG
    cfv
    #
    cF
    cfv
    wceq
    #
    @6
    @7
    wceq
    #
    cX
    cY
    wceq
    #
    @2
    @0
    @5
    @6
    cB
    wcel
    #
    @7
    cB
    wcel
    #
    wa
    #
    @8
    @9
    wi
    @0
    @1
    simpl
    @2
    @5
    @13
    @1
    @5
    @13
    wi
    #
    @0
    @1
    cA
    cB
    cG
    wf
    #
    @14
    cA
    cB
    cG
    f1f
    @15
    @3
    @11
    @4
    @12
    @15
    @3
    @11
    cA
    cB
    cX
    cG
    ffvelrn
    ex
    @15
    @4
    @12
    cA
    cB
    cY
    cG
    ffvelrn
    ex
    anim12d
    syl
    adantl
    imp
    cB
    cC
    @6
    @7
    cF
    f1veqaeq
    syl2an2r
    @1
    @5
    @9
    @10
    wi
    @0
    cA
    cB
    cX
    cY
    cG
    f1veqaeq
    adantll
    syld
end

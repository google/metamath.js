include "wf.mm"
include "wa.mm"
include "cv.mm"
include "cfv.mm"
include "wcel.mm"
include "ffvelrn.mm"
include "adantll.mm"
include "wfn.mm"
include "cmpt.mm"
include "wceq.mm"
include "ffn.mm"
include "adantl.mm"
include "dffn5.mm"
include "sylib.mm"
include "adantr.mm"
include "fveq2.mm"
include "fmptco.mm"

theorem fcompt
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cE: class E
  let vy: setvar y

  disjoint A x
  disjoint B x
  disjoint C x
  disjoint D x
  disjoint E x
  disjoint x y
  disjoint A y
  disjoint B y
  disjoint D y
  assert |- ( ( A : D --> E /\ B : C --> D ) -> ( A o. B ) = ( x e. C |-> ( A ` ( B ` x ) ) ) )

  proof
    cD
    cE
    cA
    wf
    #
    cC
    cD
    cB
    wf
    #
    wa
    #
    vx
    vy
    cC
    cD
    vx
    cv
    #
    cB
    cfv
    #
    vy
    cv
    #
    cA
    cfv
    #
    @4
    cA
    cfv
    cB
    cA
    @1
    @3
    cC
    wcel
    @4
    cD
    wcel
    @0
    cC
    cD
    @3
    cB
    ffvelrn
    adantll
    @2
    cB
    cC
    wfn
    #
    cB
    vx
    cC
    @4
    cmpt
    wceq
    @1
    @7
    @0
    cC
    cD
    cB
    ffn
    adantl
    vx
    cC
    cB
    dffn5
    sylib
    @2
    cA
    cD
    wfn
    #
    cA
    vy
    cD
    @6
    cmpt
    wceq
    @0
    @8
    @1
    cD
    cE
    cA
    ffn
    adantr
    vy
    cD
    cA
    dffn5
    sylib
    @5
    @4
    cA
    fveq2
    fmptco
end

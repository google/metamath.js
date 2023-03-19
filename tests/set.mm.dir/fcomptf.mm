include "wf.mm"
include "wa.mm"
include "cv.mm"
include "cfv.mm"
include "wcel.mm"
include "nfcv.mm"
include "nff.mm"
include "nfan.mm"
include "ffvelrn.mm"
include "adantll.mm"
include "ex.mm"
include "ralrimi.mm"
include "wfn.mm"
include "cmpt.mm"
include "wceq.mm"
include "ffn.mm"
include "adantl.mm"
include "dffn5f.mm"
include "sylib.mm"
include "adantr.mm"
include "dffn5.mm"
include "fveq2.mm"
include "fmptcof.mm"

theorem fcomptf
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cE: class E
  let vy: setvar y
  assume fcomptf.1: |- F/_ x B

  disjoint A x
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
    @2
    @4
    cD
    wcel
    #
    vx
    cC
    @0
    @1
    vx
    vx
    cD
    cE
    cA
    vx
    cA
    nfcv
    vx
    cD
    nfcv
    #
    vx
    cE
    nfcv
    nff
    vx
    cC
    cD
    cB
    fcomptf.1
    vx
    cC
    nfcv
    @8
    nff
    nfan
    @2
    @3
    cC
    wcel
    #
    @7
    @1
    @9
    @7
    @0
    cC
    cD
    @3
    cB
    ffvelrn
    adantll
    ex
    ralrimi
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
    @10
    @0
    cC
    cD
    cB
    ffn
    adantl
    vx
    cC
    cB
    fcomptf.1
    dffn5f
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
    @11
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
    fmptcof
end

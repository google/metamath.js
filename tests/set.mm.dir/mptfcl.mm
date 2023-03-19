include "cmpt.mm"
include "wf.mm"
include "wcel.mm"
include "wral.mm"
include "cv.mm"
include "wi.mm"
include "eqid.mm"
include "fmpt.mm"
include "rsp.mm"
include "sylbir.mm"

theorem mptfcl
  let vt: setvar t
  let cA: class A
  let cB: class B
  let cC: class C

  disjoint A t
  disjoint C t
  assert |- ( ( t e. A |-> B ) : A --> C -> ( t e. A -> B e. C ) )

  proof
    cA
    cC
    vt
    cA
    cB
    cmpt
    #
    wf
    cB
    cC
    wcel
    #
    vt
    cA
    wral
    vt
    cv
    cA
    wcel
    @1
    wi
    vt
    cA
    cC
    cB
    @0
    @0
    eqid
    fmpt
    @1
    vt
    cA
    rsp
    sylbir
end

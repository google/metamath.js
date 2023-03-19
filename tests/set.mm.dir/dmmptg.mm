include "wcel.mm"
include "wral.mm"
include "cvv.mm"
include "crab.mm"
include "cmpt.mm"
include "cdm.mm"
include "wceq.mm"
include "elex.mm"
include "ralimi.mm"
include "rabid2.mm"
include "sylibr.mm"
include "eqid.mm"
include "dmmpt.mm"
include "syl6reqr.mm"

theorem dmmptg
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cV: class V

  disjoint A x
  assert |- ( A. x e. A B e. V -> dom ( x e. A |-> B ) = A )

  proof
    cB
    cV
    wcel
    #
    vx
    cA
    wral
    #
    cA
    cB
    cvv
    wcel
    #
    vx
    cA
    crab
    #
    vx
    cA
    cB
    cmpt
    #
    cdm
    @1
    @2
    vx
    cA
    wral
    cA
    @3
    wceq
    @0
    @2
    vx
    cA
    cB
    cV
    elex
    ralimi
    @2
    vx
    cA
    rabid2
    sylibr
    vx
    cA
    cB
    @4
    @4
    eqid
    dmmpt
    syl6reqr
end

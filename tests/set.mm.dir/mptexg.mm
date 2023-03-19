include "wcel.mm"
include "cmpt.mm"
include "wfun.mm"
include "cdm.mm"
include "cvv.mm"
include "funmpt.mm"
include "wss.mm"
include "eqid.mm"
include "dmmptss.mm"
include "ssexg.mm"
include "mpan.mm"
include "funex.mm"
include "sylancr.mm"

theorem mptexg
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cV: class V

  disjoint A x
  assert |- ( A e. V -> ( x e. A |-> B ) e. _V )

  proof
    cA
    cV
    wcel
    #
    vx
    cA
    cB
    cmpt
    #
    wfun
    @1
    cdm
    #
    cvv
    wcel
    #
    @1
    cvv
    wcel
    vx
    cA
    cB
    funmpt
    @2
    cA
    wss
    @0
    @3
    vx
    cA
    cB
    @1
    @1
    eqid
    dmmptss
    @2
    cA
    cV
    ssexg
    mpan
    cvv
    @1
    funex
    sylancr
end

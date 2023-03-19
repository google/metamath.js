include "wrel.mm"
include "cec.mm"
include "wcel.mm"
include "wbr.mm"
include "cvv.mm"
include "wa.mm"
include "elex.mm"
include "ecexr.mm"
include "jca.mm"
include "adantl.mm"
include "brrelex12.mm"
include "ancomd.mm"
include "elecg.mm"
include "pm5.21nd.mm"

theorem relelec
  let cA: class A
  let cB: class B
  let cR: class R


  assert |- ( Rel R -> ( A e. [ B ] R <-> B R A ) )

  proof
    cR
    wrel
    #
    cA
    cB
    cR
    cec
    #
    wcel
    #
    cB
    cA
    cR
    wbr
    #
    cA
    cvv
    wcel
    #
    cB
    cvv
    wcel
    #
    wa
    #
    @2
    @6
    @0
    @2
    @4
    @5
    cA
    @1
    elex
    cA
    cB
    cR
    ecexr
    jca
    adantl
    @0
    @3
    wa
    @5
    @4
    cB
    cA
    cR
    brrelex12
    ancomd
    cA
    cB
    cR
    cvv
    cvv
    elecg
    pm5.21nd
end

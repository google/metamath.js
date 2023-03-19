include "wrel.mm"
include "wbr.mm"
include "wa.mm"
include "cvv.mm"
include "wcel.mm"
include "crn.mm"
include "brrelex.mm"
include "brrelex2.mm"
include "simpr.mm"
include "brelrng.mm"
include "syl3anc.mm"

theorem relelrn
  let cA: class A
  let cB: class B
  let cR: class R


  assert |- ( ( Rel R /\ A R B ) -> B e. ran R )

  proof
    cR
    wrel
    #
    cA
    cB
    cR
    wbr
    #
    wa
    cA
    cvv
    wcel
    cB
    cvv
    wcel
    @1
    cB
    cR
    crn
    wcel
    cA
    cB
    cR
    brrelex
    cA
    cB
    cR
    brrelex2
    @0
    @1
    simpr
    cA
    cB
    cR
    cvv
    cvv
    brelrng
    syl3anc
end

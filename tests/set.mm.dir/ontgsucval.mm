include "con0.mm"
include "wcel.mm"
include "csuc.mm"
include "ctg.mm"
include "cfv.mm"
include "cuni.mm"
include "wceq.mm"
include "suceloni.mm"
include "ontgval.mm"
include "syl.mm"
include "word.mm"
include "eloni.mm"
include "ordunisuc.mm"
include "suceq.mm"
include "eqtrd.mm"

theorem ontgsucval
  let cA: class A


  assert |- ( A e. On -> ( topGen ` suc A ) = suc A )

  proof
    cA
    con0
    wcel
    #
    cA
    csuc
    #
    ctg
    cfv
    #
    @1
    cuni
    #
    csuc
    #
    @1
    @0
    @1
    con0
    wcel
    @2
    @4
    wceq
    cA
    suceloni
    @1
    ontgval
    syl
    @0
    @3
    cA
    wceq
    #
    @4
    @1
    wceq
    @0
    cA
    word
    @5
    cA
    eloni
    cA
    ordunisuc
    syl
    @3
    cA
    suceq
    syl
    eqtrd
end

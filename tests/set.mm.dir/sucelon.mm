include "word.mm"
include "cvv.mm"
include "wcel.mm"
include "wa.mm"
include "csuc.mm"
include "con0.mm"
include "ordsuc.mm"
include "sucexb.mm"
include "anbi12i.mm"
include "elon2.mm"
include "3bitr4i.mm"

theorem sucelon
  let cA: class A


  assert |- ( A e. On <-> suc A e. On )

  proof
    cA
    word
    #
    cA
    cvv
    wcel
    #
    wa
    cA
    csuc
    #
    word
    #
    @2
    cvv
    wcel
    #
    wa
    cA
    con0
    wcel
    @2
    con0
    wcel
    @0
    @3
    @1
    @4
    cA
    ordsuc
    cA
    sucexb
    anbi12i
    cA
    elon2
    @2
    elon2
    3bitr4i
end

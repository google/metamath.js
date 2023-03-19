include "con0.mm"
include "wcel.mm"
include "wa.mm"
include "cin.mm"
include "word.mm"
include "eloni.mm"
include "ordin.mm"
include "syl2an.mm"
include "cvv.mm"
include "wb.mm"
include "simpl.mm"
include "inex1g.mm"
include "elong.mm"
include "3syl.mm"
include "mpbird.mm"

theorem onin
  let cA: class A
  let cB: class B


  assert |- ( ( A e. On /\ B e. On ) -> ( A i^i B ) e. On )

  proof
    cA
    con0
    wcel
    #
    cB
    con0
    wcel
    #
    wa
    #
    cA
    cB
    cin
    #
    con0
    wcel
    #
    @3
    word
    #
    @0
    cA
    word
    cB
    word
    @5
    @1
    cA
    eloni
    cB
    eloni
    cA
    cB
    ordin
    syl2an
    @2
    @0
    @3
    cvv
    wcel
    @4
    @5
    wb
    @0
    @1
    simpl
    cA
    cB
    con0
    inex1g
    @3
    cvv
    elong
    3syl
    mpbird
end

include "word.mm"
include "wcel.mm"
include "wa.mm"
include "con0.mm"
include "ordelord.mm"
include "wb.mm"
include "elong.mm"
include "adantl.mm"
include "mpbird.mm"

theorem ordelon
  let cA: class A
  let cB: class B


  assert |- ( ( Ord A /\ B e. A ) -> B e. On )

  proof
    cA
    word
    #
    cB
    cA
    wcel
    #
    wa
    cB
    con0
    wcel
    #
    cB
    word
    #
    cA
    cB
    ordelord
    @1
    @2
    @3
    wb
    @0
    cB
    cA
    elong
    adantl
    mpbird
end

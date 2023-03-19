include "con0.mm"
include "wss.mm"
include "cuni.mm"
include "wcel.mm"
include "word.mm"
include "ssorduni.mm"
include "cvv.mm"
include "wb.mm"
include "uniexg.mm"
include "elong.mm"
include "syl.mm"
include "syl5ibr.mm"

theorem ssonuni
  let cA: class A
  let cV: class V


  assert |- ( A e. V -> ( A C_ On -> U. A e. On ) )

  proof
    cA
    con0
    wss
    cA
    cuni
    #
    con0
    wcel
    #
    cA
    cV
    wcel
    #
    @0
    word
    #
    cA
    ssorduni
    @2
    @0
    cvv
    wcel
    @1
    @3
    wb
    cA
    cV
    uniexg
    @0
    cvv
    elong
    syl
    syl5ibr
end

include "wcel.mm"
include "cpw.mm"
include "wss.mm"
include "cuni.mm"
include "elpwg.mm"
include "wb.mm"
include "sspwuni.mm"
include "a1i.mm"
include "cvv.mm"
include "uniexg.mm"
include "syl.mm"
include "bicomd.mm"
include "3bitrd.mm"

theorem pwpwuni
  let cA: class A
  let cB: class B
  let cV: class V


  assert |- ( A e. V -> ( A e. ~P ~P B <-> U. A e. ~P B ) )

  proof
    cA
    cV
    wcel
    #
    cA
    cB
    cpw
    #
    cpw
    wcel
    cA
    @1
    wss
    #
    cA
    cuni
    #
    cB
    wss
    #
    @3
    @1
    wcel
    #
    cA
    @1
    cV
    elpwg
    @2
    @4
    wb
    @0
    cA
    cB
    sspwuni
    a1i
    @0
    @5
    @4
    @0
    @3
    cvv
    wcel
    @5
    @4
    wb
    cA
    cV
    uniexg
    @3
    cB
    cvv
    elpwg
    syl
    bicomd
    3bitrd
end

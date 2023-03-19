include "cc0.mm"
include "clt.mm"
include "wbr.mm"
include "cr.mm"
include "wcel.mm"
include "cdiv.mm"
include "co.mm"
include "wb.mm"
include "wa.mm"
include "ltdiv23.mm"
include "mp3an1.mm"
include "mpanl1.mm"
include "mpanr1.mm"

theorem ltdiv23i
  let cA: class A
  let cB: class B
  let cC: class C
  assume ltplus1.1: |- A e. RR
  assume prodgt0.2: |- B e. RR
  assume ltmul1.3: |- C e. RR


  assert |- ( ( 0 < B /\ 0 < C ) -> ( ( A / B ) < C <-> ( A / C ) < B ) )

  proof
    cc0
    cB
    clt
    wbr
    #
    cC
    cr
    wcel
    #
    cc0
    cC
    clt
    wbr
    #
    cA
    cB
    cdiv
    co
    cC
    clt
    wbr
    cA
    cC
    cdiv
    co
    cB
    clt
    wbr
    wb
    #
    ltmul1.3
    cB
    cr
    wcel
    #
    @0
    @1
    @2
    wa
    #
    @3
    prodgt0.2
    cA
    cr
    wcel
    @4
    @0
    wa
    @5
    @3
    ltplus1.1
    cA
    cB
    cC
    ltdiv23
    mp3an1
    mpanl1
    mpanr1
end

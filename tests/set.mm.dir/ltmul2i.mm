include "cr.mm"
include "wcel.mm"
include "cc0.mm"
include "clt.mm"
include "wbr.mm"
include "cmul.mm"
include "co.mm"
include "wb.mm"
include "wa.mm"
include "ltmul2.mm"
include "mp3an12.mm"
include "mpan.mm"

theorem ltmul2i
  let cA: class A
  let cB: class B
  let cC: class C
  assume ltplus1.1: |- A e. RR
  assume prodgt0.2: |- B e. RR
  assume ltmul1.3: |- C e. RR


  assert |- ( 0 < C -> ( A < B <-> ( C x. A ) < ( C x. B ) ) )

  proof
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
    clt
    wbr
    cC
    cA
    cmul
    co
    cC
    cB
    cmul
    co
    clt
    wbr
    wb
    #
    ltmul1.3
    cA
    cr
    wcel
    cB
    cr
    wcel
    @0
    @1
    wa
    @2
    ltplus1.1
    prodgt0.2
    cA
    cB
    cC
    ltmul2
    mp3an12
    mpan
end

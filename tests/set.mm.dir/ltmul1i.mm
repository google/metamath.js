include "cr.mm"
include "wcel.mm"
include "cc0.mm"
include "clt.mm"
include "wbr.mm"
include "cmul.mm"
include "co.mm"
include "wb.mm"
include "wa.mm"
include "ltmul1.mm"
include "mp3an12.mm"
include "mpan.mm"

theorem ltmul1i
  let cA: class A
  let cB: class B
  let cC: class C
  assume ltplus1.1: |- A e. RR
  assume prodgt0.2: |- B e. RR
  assume ltmul1.3: |- C e. RR


  assert |- ( 0 < C -> ( A < B <-> ( A x. C ) < ( B x. C ) ) )

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
    cA
    cC
    cmul
    co
    cB
    cC
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
    ltmul1
    mp3an12
    mpan
end

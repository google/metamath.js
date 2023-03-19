include "cr.mm"
include "wcel.mm"
include "clt.mm"
include "wbr.mm"
include "caddc.mm"
include "co.mm"
include "wb.mm"
include "ltadd2.mm"
include "mp3an.mm"

theorem ltadd2i
  let cA: class A
  let cB: class B
  let cC: class C
  assume lt.1: |- A e. RR
  assume lt.2: |- B e. RR
  assume lt.3: |- C e. RR


  assert |- ( A < B <-> ( C + A ) < ( C + B ) )

  proof
    cA
    cr
    wcel
    cB
    cr
    wcel
    cC
    cr
    wcel
    cA
    cB
    clt
    wbr
    cC
    cA
    caddc
    co
    cC
    cB
    caddc
    co
    clt
    wbr
    wb
    lt.1
    lt.2
    lt.3
    cA
    cB
    cC
    ltadd2
    mp3an
end

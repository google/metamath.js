include "cc0.mm"
include "clt.mm"
include "wbr.mm"
include "c1.mm"
include "cdiv.mm"
include "co.mm"
include "wb.mm"
include "ltreci.mm"
include "mp2an.mm"

theorem ltrecii
  let cA: class A
  let cB: class B
  assume ltplus1.1: |- A e. RR
  assume prodgt0.2: |- B e. RR
  assume ltreci.3: |- 0 < A
  assume ltreci.4: |- 0 < B


  assert |- ( A < B <-> ( 1 / B ) < ( 1 / A ) )

  proof
    cc0
    cA
    clt
    wbr
    cc0
    cB
    clt
    wbr
    cA
    cB
    clt
    wbr
    c1
    cB
    cdiv
    co
    c1
    cA
    cdiv
    co
    clt
    wbr
    wb
    ltreci.3
    ltreci.4
    cA
    cB
    ltplus1.1
    prodgt0.2
    ltreci
    mp2an
end

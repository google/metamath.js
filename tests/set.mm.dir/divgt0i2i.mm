include "cc0.mm"
include "clt.mm"
include "wbr.mm"
include "cdiv.mm"
include "co.mm"
include "divgt0i.mm"
include "mpan2.mm"

theorem divgt0i2i
  let cA: class A
  let cB: class B
  assume ltplus1.1: |- A e. RR
  assume prodgt0.2: |- B e. RR
  assume divgt0i2.3: |- 0 < B


  assert |- ( 0 < A -> 0 < ( A / B ) )

  proof
    cc0
    cA
    clt
    wbr
    cc0
    cB
    clt
    wbr
    cc0
    cA
    cB
    cdiv
    co
    clt
    wbr
    divgt0i2.3
    cA
    cB
    ltplus1.1
    prodgt0.2
    divgt0i
    mpan2
end

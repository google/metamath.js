include "cc0.mm"
include "clt.mm"
include "wbr.mm"
include "cmul.mm"
include "co.mm"
include "mulgt0i.mm"
include "mp2an.mm"

theorem mulgt0ii
  let cA: class A
  let cB: class B
  assume lt.1: |- A e. RR
  assume lt.2: |- B e. RR
  assume mulgt0i.3: |- 0 < A
  assume mulgt0i.4: |- 0 < B


  assert |- 0 < ( A x. B )

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
    cmul
    co
    clt
    wbr
    mulgt0i.3
    mulgt0i.4
    cA
    cB
    lt.1
    lt.2
    mulgt0i
    mp2an
end

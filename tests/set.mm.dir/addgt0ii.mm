include "cc0.mm"
include "clt.mm"
include "wbr.mm"
include "caddc.mm"
include "co.mm"
include "addgt0i.mm"
include "mp2an.mm"

theorem addgt0ii
  let cA: class A
  let cB: class B
  assume lt2.1: |- A e. RR
  assume lt2.2: |- B e. RR
  assume addgt0i.3: |- 0 < A
  assume addgt0i.4: |- 0 < B


  assert |- 0 < ( A + B )

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
    caddc
    co
    clt
    wbr
    addgt0i.3
    addgt0i.4
    cA
    cB
    lt2.1
    lt2.2
    addgt0i
    mp2an
end

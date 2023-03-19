include "cc0.mm"
include "clt.mm"
include "wbr.mm"
include "cdiv.mm"
include "co.mm"
include "wb.mm"
include "ltdiv23i.mm"
include "mp2an.mm"

theorem ltdiv23ii
  let cA: class A
  let cB: class B
  let cC: class C
  assume ltplus1.1: |- A e. RR
  assume prodgt0.2: |- B e. RR
  assume ltmul1.3: |- C e. RR
  assume ltdiv23i.4: |- 0 < B
  assume ltdiv23i.5: |- 0 < C


  assert |- ( ( A / B ) < C <-> ( A / C ) < B )

  proof
    cc0
    cB
    clt
    wbr
    cc0
    cC
    clt
    wbr
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
    ltdiv23i.4
    ltdiv23i.5
    cA
    cB
    cC
    ltplus1.1
    prodgt0.2
    ltmul1.3
    ltdiv23i
    mp2an
end

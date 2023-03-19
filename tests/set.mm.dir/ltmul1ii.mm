include "cc0.mm"
include "clt.mm"
include "wbr.mm"
include "cmul.mm"
include "co.mm"
include "wb.mm"
include "ltmul1i.mm"
include "ax-mp.mm"

theorem ltmul1ii
  let cA: class A
  let cB: class B
  let cC: class C
  assume ltplus1.1: |- A e. RR
  assume prodgt0.2: |- B e. RR
  assume ltmul1.3: |- C e. RR
  assume ltmul1i.4: |- 0 < C


  assert |- ( A < B <-> ( A x. C ) < ( B x. C ) )

  proof
    cc0
    cC
    clt
    wbr
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
    ltmul1i.4
    cA
    cB
    cC
    ltplus1.1
    prodgt0.2
    ltmul1.3
    ltmul1i
    ax-mp
end

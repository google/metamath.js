include "cfne.mm"
include "wbr.mm"
include "wceq.mm"
include "ctg.mm"
include "cfv.mm"
include "wss.mm"
include "isfne4.mm"
include "simplbi.mm"

theorem fnebas
  let cA: class A
  let cB: class B
  let cX: class X
  let cY: class Y
  assume fnebas.1: |- X = U. A
  assume fnebas.2: |- Y = U. B


  assert |- ( A Fne B -> X = Y )

  proof
    cA
    cB
    cfne
    wbr
    cX
    cY
    wceq
    cA
    cB
    ctg
    cfv
    wss
    cA
    cB
    cX
    cY
    fnebas.1
    fnebas.2
    isfne4
    simplbi
end

include "con0.mm"
include "wcel.mm"
include "word.mm"
include "csuc.mm"
include "wss.mm"
include "wb.mm"
include "onordi.mm"
include "ordelsuc.mm"
include "mp2an.mm"

theorem onsucssi
  let cA: class A
  let cB: class B
  assume onssi.1: |- A e. On
  assume onsucssi.2: |- B e. On


  assert |- ( A e. B <-> suc A C_ B )

  proof
    cA
    con0
    wcel
    cB
    word
    cA
    cB
    wcel
    cA
    csuc
    cB
    wss
    wb
    onssi.1
    cB
    onsucssi.2
    onordi
    cA
    cB
    con0
    ordelsuc
    mp2an
end

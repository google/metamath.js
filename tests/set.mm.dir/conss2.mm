include "cvv.mm"
include "wss.mm"
include "cdif.mm"
include "wb.mm"
include "ssv.mm"
include "ssconb.mm"
include "mp2an.mm"

theorem conss2
  let cA: class A
  let cB: class B
  let vx: setvar x


  assert |- ( A C_ ( _V \ B ) <-> B C_ ( _V \ A ) )

  proof
    cA
    cvv
    wss
    cB
    cvv
    wss
    cA
    cvv
    cB
    cdif
    wss
    cB
    cvv
    cA
    cdif
    wss
    wb
    cA
    ssv
    cB
    ssv
    cA
    cB
    cvv
    ssconb
    mp2an
end

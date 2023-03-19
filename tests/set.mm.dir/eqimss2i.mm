include "ssid.mm"
include "sseqtr4i.mm"

theorem eqimss2i
  let cA: class A
  let cB: class B
  assume eqimssi.1: |- A = B


  assert |- B C_ A

  proof
    cB
    cB
    cA
    cB
    ssid
    eqimssi.1
    sseqtr4i
end

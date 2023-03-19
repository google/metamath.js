include "ssid.mm"
include "sseqtri.mm"

theorem eqimssi
  let cA: class A
  let cB: class B
  assume eqimssi.1: |- A = B


  assert |- A C_ B

  proof
    cA
    cA
    cB
    cA
    ssid
    eqimssi.1
    sseqtri
end

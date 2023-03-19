include "cwina.mm"
include "wcel.mm"
include "com.mm"
include "wne.mm"
include "cale.mm"
include "cfv.mm"
include "wceq.mm"
include "winafp.mm"
include "mp2an.mm"

theorem winafpi
  let cA: class A
  assume winafp.1: |- A e. InaccW
  assume winafp.2: |- A =/= _om


  assert |- ( aleph ` A ) = A

  proof
    cA
    cwina
    wcel
    cA
    com
    wne
    cA
    cale
    cfv
    cA
    wceq
    winafp.1
    winafp.2
    cA
    winafp
    mp2an
end

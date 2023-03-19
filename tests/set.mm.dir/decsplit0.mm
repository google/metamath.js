include "c1.mm"
include "cc0.mm"
include "cdc.mm"
include "cexp.mm"
include "co.mm"
include "cmul.mm"
include "caddc.mm"
include "decsplit0b.mm"
include "nn0cni.mm"
include "addid1i.mm"
include "eqtri.mm"

theorem decsplit0
  let cA: class A
  assume decsplit0.1: |- A e. NN0


  assert |- ( ( A x. ( ; 1 0 ^ 0 ) ) + 0 ) = A

  proof
    cA
    c1
    cc0
    cdc
    cc0
    cexp
    co
    cmul
    co
    cc0
    caddc
    co
    cA
    cc0
    caddc
    co
    cA
    cA
    cc0
    decsplit0.1
    decsplit0b
    cA
    cA
    decsplit0.1
    nn0cni
    addid1i
    eqtri
end

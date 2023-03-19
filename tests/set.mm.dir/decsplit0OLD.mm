include "c10.mm"
include "cc0.mm"
include "cexp.mm"
include "co.mm"
include "cmul.mm"
include "caddc.mm"
include "decsplit0bOLD.mm"
include "nn0cni.mm"
include "addid1i.mm"
include "eqtri.mm"

theorem decsplit0OLD
  let cA: class A
  assume decsplit0OLD.1: |- A e. NN0


  assert |- ( ( A x. ( 10 ^ 0 ) ) + 0 ) = A

  proof
    cA
    c10
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
    decsplit0OLD.1
    decsplit0bOLD
    cA
    cA
    decsplit0OLD.1
    nn0cni
    addid1i
    eqtri
end

include "c10.mm"
include "cc0.mm"
include "cexp.mm"
include "co.mm"
include "cmul.mm"
include "caddc.mm"
include "c1.mm"
include "10nn0OLD.mm"
include "numexp0.mm"
include "oveq2i.mm"
include "nn0cni.mm"
include "mulid1i.mm"
include "eqtri.mm"
include "oveq1i.mm"

theorem decsplit0bOLD
  let cA: class A
  let cB: class B
  assume decsplit0OLD.1: |- A e. NN0


  assert |- ( ( A x. ( 10 ^ 0 ) ) + B ) = ( A + B )

  proof
    cA
    c10
    cc0
    cexp
    co
    #
    cmul
    co
    #
    cA
    cB
    caddc
    @1
    cA
    c1
    cmul
    co
    cA
    @0
    c1
    cA
    cmul
    c10
    10nn0OLD
    numexp0
    oveq2i
    cA
    cA
    decsplit0OLD.1
    nn0cni
    mulid1i
    eqtri
    oveq1i
end

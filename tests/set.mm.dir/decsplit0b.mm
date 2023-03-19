include "c1.mm"
include "cc0.mm"
include "cdc.mm"
include "cexp.mm"
include "co.mm"
include "cmul.mm"
include "caddc.mm"
include "10nn0.mm"
include "numexp0.mm"
include "oveq2i.mm"
include "nn0cni.mm"
include "mulid1i.mm"
include "eqtri.mm"
include "oveq1i.mm"

theorem decsplit0b
  let cA: class A
  let cB: class B
  assume decsplit0.1: |- A e. NN0


  assert |- ( ( A x. ( ; 1 0 ^ 0 ) ) + B ) = ( A + B )

  proof
    cA
    c1
    cc0
    cdc
    #
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
    @2
    cA
    c1
    cmul
    co
    cA
    @1
    c1
    cA
    cmul
    @0
    10nn0
    numexp0
    oveq2i
    cA
    cA
    decsplit0.1
    nn0cni
    mulid1i
    eqtri
    oveq1i
end

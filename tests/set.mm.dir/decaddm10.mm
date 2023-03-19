include "cc0.mm"
include "caddc.mm"
include "co.mm"
include "cdc.mm"
include "0nn0.mm"
include "eqid.mm"
include "00id.mm"
include "decadd.mm"

theorem decaddm10
  let cA: class A
  let cB: class B
  assume decaddm10.a: |- A e. NN0
  assume decaddm10.b: |- B e. NN0


  assert |- ( ; A 0 + ; B 0 ) = ; ( A + B ) 0

  proof
    cA
    cc0
    cB
    cc0
    cA
    cB
    caddc
    co
    #
    cc0
    cA
    cc0
    cdc
    #
    cB
    cc0
    cdc
    #
    decaddm10.a
    0nn0
    decaddm10.b
    0nn0
    @1
    eqid
    @2
    eqid
    @0
    eqid
    00id
    decadd
end

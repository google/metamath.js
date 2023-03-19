include "cmul.mm"
include "co.mm"
include "cc0.mm"
include "cdc.mm"
include "eqid.mm"
include "nn0mulcli.mm"
include "0nn0.mm"
include "nn0cni.mm"
include "addid1i.mm"
include "dec0h.mm"
include "decmul2c.mm"

theorem decmulnc
  let cA: class A
  let cB: class B
  let cN: class N
  assume decmulnc.n: |- N e. NN0
  assume decmulnc.a: |- A e. NN0
  assume decmulnc.b: |- B e. NN0


  assert |- ( N x. ; A B ) = ; ( N x. A ) ( N x. B )

  proof
    cA
    cB
    cN
    cA
    cmul
    co
    #
    cN
    cB
    cmul
    co
    #
    cN
    cc0
    cA
    cB
    cdc
    #
    decmulnc.n
    decmulnc.a
    decmulnc.b
    @2
    eqid
    cN
    cB
    decmulnc.n
    decmulnc.b
    nn0mulcli
    #
    0nn0
    @0
    @0
    cN
    cA
    decmulnc.n
    decmulnc.a
    nn0mulcli
    nn0cni
    addid1i
    @1
    @3
    dec0h
    decmul2c
end

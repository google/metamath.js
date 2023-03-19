include "c2.mm"
include "cmul.mm"
include "co.mm"
include "c1.mm"
include "caddc.mm"
include "c5.mm"
include "cdc.mm"
include "cn.mm"
include "wcel.mm"
include "2nn.mm"
include "nnmulcli.mm"
include "peano2nn.mm"
include "ax-mp.mm"
include "5nn.mm"
include "1nn0.mm"
include "1lt2.mm"
include "numlti.mm"
include "1lt5.mm"
include "cc0.mm"
include "nncni.mm"
include "5cn.mm"
include "mul32i.mm"
include "5t2e10.mm"
include "mulcomli.mm"
include "oveq1i.mm"
include "eqtri.mm"
include "mulid2i.mm"
include "oveq12i.mm"
include "ax-1cn.mm"
include "adddiri.mm"
include "dfdec10.mm"
include "3eqtr4i.mm"
include "nprmi.mm"

theorem dec5nprm
  let cA: class A
  assume dec5nprm.1: |- A e. NN


  assert |- -. ; A 5 e. Prime

  proof
    c2
    cA
    cmul
    co
    #
    c1
    caddc
    co
    #
    c5
    cA
    c5
    cdc
    #
    @0
    cn
    wcel
    @1
    cn
    wcel
    c2
    cA
    2nn
    dec5nprm.1
    nnmulcli
    #
    @0
    peano2nn
    ax-mp
    5nn
    cA
    c1
    c1
    c2
    2nn
    dec5nprm.1
    1nn0
    1nn0
    1lt2
    numlti
    1lt5
    @0
    c5
    cmul
    co
    #
    c1
    c5
    cmul
    co
    #
    caddc
    co
    c1
    cc0
    cdc
    #
    cA
    cmul
    co
    #
    c5
    caddc
    co
    @1
    c5
    cmul
    co
    @2
    @4
    @7
    @5
    c5
    caddc
    @4
    c2
    c5
    cmul
    co
    #
    cA
    cmul
    co
    @7
    c2
    cA
    c5
    c2
    2nn
    nncni
    #
    cA
    dec5nprm.1
    nncni
    5cn
    mul32i
    @8
    @6
    cA
    cmul
    c5
    c2
    @6
    5cn
    @9
    5t2e10
    mulcomli
    oveq1i
    eqtri
    c5
    5cn
    mulid2i
    oveq12i
    @0
    c1
    c5
    @0
    @3
    nncni
    ax-1cn
    5cn
    adddiri
    cA
    c5
    dfdec10
    3eqtr4i
    nprmi
end

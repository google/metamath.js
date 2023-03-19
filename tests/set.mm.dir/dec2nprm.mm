include "c5.mm"
include "cmul.mm"
include "co.mm"
include "caddc.mm"
include "c2.mm"
include "cdc.mm"
include "cn.mm"
include "wcel.mm"
include "cn0.mm"
include "5nn.mm"
include "nnmulcli.mm"
include "nnnn0addcl.mm"
include "mp2an.mm"
include "2nn.mm"
include "c1.mm"
include "1nn0.mm"
include "1lt5.mm"
include "numlti.mm"
include "1lt2.mm"
include "cc0.mm"
include "nncni.mm"
include "2cn.mm"
include "mul32i.mm"
include "5t2e10.mm"
include "oveq1i.mm"
include "eqtri.mm"
include "oveq12i.mm"
include "nn0cni.mm"
include "adddiri.mm"
include "dfdec10.mm"
include "3eqtr4i.mm"
include "nprmi.mm"

theorem dec2nprm
  let cA: class A
  let cB: class B
  let cC: class C
  assume dec5nprm.1: |- A e. NN
  assume dec2nprm.2: |- B e. NN0
  assume dec2nprm.3: |- ( B x. 2 ) = C


  assert |- -. ; A C e. Prime

  proof
    c5
    cA
    cmul
    co
    #
    cB
    caddc
    co
    #
    c2
    cA
    cC
    cdc
    #
    @0
    cn
    wcel
    cB
    cn0
    wcel
    @1
    cn
    wcel
    c5
    cA
    5nn
    dec5nprm.1
    nnmulcli
    #
    dec2nprm.2
    @0
    cB
    nnnn0addcl
    mp2an
    2nn
    cA
    cB
    c1
    c5
    5nn
    dec5nprm.1
    dec2nprm.2
    1nn0
    1lt5
    numlti
    1lt2
    @0
    c2
    cmul
    co
    #
    cB
    c2
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
    cC
    caddc
    co
    @1
    c2
    cmul
    co
    @2
    @4
    @7
    @5
    cC
    caddc
    @4
    c5
    c2
    cmul
    co
    #
    cA
    cmul
    co
    @7
    c5
    cA
    c2
    c5
    5nn
    nncni
    cA
    dec5nprm.1
    nncni
    2cn
    mul32i
    @8
    @6
    cA
    cmul
    5t2e10
    oveq1i
    eqtri
    dec2nprm.3
    oveq12i
    @0
    cB
    c2
    @0
    @3
    nncni
    cB
    dec2nprm.2
    nn0cni
    2cn
    adddiri
    cA
    cC
    dfdec10
    3eqtr4i
    nprmi
end

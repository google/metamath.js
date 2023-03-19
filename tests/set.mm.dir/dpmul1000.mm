include "cdc.mm"
include "cdp2.mm"
include "c1.mm"
include "cc0.mm"
include "cmul.mm"
include "co.mm"
include "cdp.mm"
include "cn0.mm"
include "wcel.mm"
include "cr.mm"
include "nn0rei.mm"
include "dp2cl.mm"
include "mp2an.mm"
include "dpcl.mm"
include "recni.mm"
include "10nn0.mm"
include "0nn0.mm"
include "deccl.mm"
include "nn0cni.mm"
include "mulassi.mm"
include "dpmul100.mm"
include "oveq1i.mm"
include "dec0u.mm"
include "mulcomli.mm"
include "oveq2i.mm"
include "3eqtr3i.mm"
include "caddc.mm"
include "dfdec10.mm"
include "mulcli.mm"
include "adddiri.mm"
include "dfdec100.mm"
include "mul32i.mm"
include "eqtr3i.mm"
include "dpmul10.mm"
include "wceq.mm"
include "dpval.mm"
include "oveq12i.mm"
include "eqtr2i.mm"
include "3eqtri.mm"

theorem dpmul1000
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  assume dpmul1000.a: |- A e. NN0
  assume dpmul1000.b: |- B e. NN0
  assume dpmul1000.c: |- C e. NN0
  assume dpmul1000.d: |- D e. RR


  assert |- ( ( A . _ B _ C D ) x. ; ; ; 1 0 0 0 ) = ; ; ; A B C D

  proof
    cA
    cB
    cdc
    #
    cC
    cD
    cdp2
    #
    cdc
    #
    c1
    cc0
    cdc
    #
    cmul
    co
    #
    cA
    cB
    @1
    cdp2
    #
    cdp
    co
    #
    @3
    cc0
    cdc
    #
    cc0
    cdc
    #
    cmul
    co
    #
    @0
    cC
    cdc
    cD
    cdc
    #
    @6
    @7
    cmul
    co
    #
    @3
    cmul
    co
    @6
    @7
    @3
    cmul
    co
    #
    cmul
    co
    @4
    @9
    @6
    @7
    @3
    @6
    cA
    cn0
    wcel
    @5
    cr
    wcel
    #
    @6
    cr
    wcel
    dpmul1000.a
    cB
    cr
    wcel
    @1
    cr
    wcel
    #
    @13
    cB
    dpmul1000.b
    nn0rei
    cC
    cr
    wcel
    cD
    cr
    wcel
    #
    @14
    cC
    dpmul1000.c
    nn0rei
    dpmul1000.d
    cC
    cD
    dp2cl
    mp2an
    #
    cB
    @1
    dp2cl
    mp2an
    cA
    @5
    dpcl
    mp2an
    recni
    @7
    @3
    cc0
    10nn0
    0nn0
    deccl
    #
    nn0cni
    #
    @3
    10nn0
    nn0cni
    #
    mulassi
    @11
    @2
    @3
    cmul
    cA
    cB
    @1
    dpmul1000.a
    dpmul1000.b
    @16
    dpmul100
    oveq1i
    @12
    @8
    @6
    cmul
    @3
    @7
    @8
    @19
    @18
    @7
    @17
    dec0u
    mulcomli
    oveq2i
    3eqtr3i
    @4
    @3
    @0
    cmul
    co
    #
    @1
    caddc
    co
    #
    @3
    cmul
    co
    @20
    @3
    cmul
    co
    #
    @1
    @3
    cmul
    co
    #
    caddc
    co
    #
    @10
    @2
    @21
    @3
    cmul
    @0
    @1
    dfdec10
    oveq1i
    @20
    @1
    @3
    @3
    @0
    @19
    @0
    cA
    cB
    dpmul1000.a
    dpmul1000.b
    deccl
    #
    nn0cni
    #
    mulcli
    @1
    @16
    recni
    @19
    adddiri
    @10
    @7
    @0
    cmul
    co
    #
    cC
    cD
    cdc
    #
    caddc
    co
    @24
    @0
    cC
    cD
    @25
    dpmul1000.c
    dpmul1000.d
    dfdec100
    @27
    @22
    @28
    @23
    caddc
    @3
    @3
    cmul
    co
    #
    @0
    cmul
    co
    @27
    @22
    @29
    @7
    @0
    cmul
    @3
    10nn0
    dec0u
    oveq1i
    @3
    @3
    @0
    @19
    @19
    @26
    mul32i
    eqtr3i
    cC
    cD
    cdp
    co
    #
    @3
    cmul
    co
    @28
    @23
    cC
    cD
    dpmul1000.c
    dpmul1000.d
    dpmul10
    @30
    @1
    @3
    cmul
    cC
    cn0
    wcel
    @15
    @30
    @1
    wceq
    dpmul1000.c
    dpmul1000.d
    cC
    cD
    dpval
    mp2an
    oveq1i
    eqtr3i
    oveq12i
    eqtr2i
    3eqtri
    eqtr3i
end

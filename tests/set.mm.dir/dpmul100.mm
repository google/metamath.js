include "cdp2.mm"
include "cdp.mm"
include "co.mm"
include "c1.mm"
include "cc0.mm"
include "cdc.mm"
include "cmul.mm"
include "cdiv.mm"
include "caddc.mm"
include "cc.mm"
include "cr.mm"
include "wcel.mm"
include "nn0rei.mm"
include "dp2cl.mm"
include "mp2an.mm"
include "dpval2.mm"
include "nn0cni.mm"
include "recni.mm"
include "10nn0.mm"
include "10nn.mm"
include "nnne0i.mm"
include "divcli.mm"
include "addcli.mm"
include "eqeltri.mm"
include "mulassi.mm"
include "dfdec100.mm"
include "mul32i.mm"
include "dec0u.mm"
include "oveq1i.mm"
include "eqtri.mm"
include "dpval3.mm"
include "dpmul10.mm"
include "eqtr3i.mm"
include "oveq12i.mm"
include "dfdec10.mm"
include "mulcli.mm"
include "adddiri.mm"
include "eqtr2i.mm"
include "3eqtr2ri.mm"
include "oveq2i.mm"
include "3eqtr3ri.mm"

theorem dpmul100
  let cA: class A
  let cB: class B
  let cC: class C
  assume dp3mul10.a: |- A e. NN0
  assume dp3mul10.b: |- B e. NN0
  assume dp3mul10.c: |- C e. RR


  assert |- ( ( A . _ B C ) x. ; ; 1 0 0 ) = ; ; A B C

  proof
    cA
    cB
    cC
    cdp2
    #
    cdp
    co
    #
    c1
    cc0
    cdc
    #
    cmul
    co
    #
    @2
    cmul
    co
    #
    @1
    @2
    @2
    cmul
    co
    #
    cmul
    co
    cA
    cB
    cdc
    cC
    cdc
    #
    @1
    @2
    cc0
    cdc
    #
    cmul
    co
    @1
    @2
    @2
    @1
    cA
    @0
    @2
    cdiv
    co
    #
    caddc
    co
    cc
    cA
    @0
    dp3mul10.a
    cB
    cr
    wcel
    cC
    cr
    wcel
    @0
    cr
    wcel
    cB
    dp3mul10.b
    nn0rei
    dp3mul10.c
    cB
    cC
    dp2cl
    mp2an
    #
    dpval2
    cA
    @8
    cA
    dp3mul10.a
    nn0cni
    #
    @0
    @2
    @0
    @9
    recni
    #
    @2
    10nn0
    nn0cni
    #
    @2
    10nn
    nnne0i
    divcli
    addcli
    eqeltri
    @12
    @12
    mulassi
    @6
    @7
    cA
    cmul
    co
    #
    cB
    cC
    cdc
    #
    caddc
    co
    @2
    cA
    cmul
    co
    #
    @2
    cmul
    co
    #
    @0
    @2
    cmul
    co
    #
    caddc
    co
    #
    @4
    cA
    cB
    cC
    dp3mul10.a
    dp3mul10.b
    dp3mul10.c
    dfdec100
    @16
    @13
    @17
    @14
    caddc
    @16
    @5
    cA
    cmul
    co
    @13
    @2
    cA
    @2
    @12
    @10
    @12
    mul32i
    @5
    @7
    cA
    cmul
    @2
    10nn0
    dec0u
    #
    oveq1i
    eqtri
    cB
    cC
    cdp
    co
    #
    @2
    cmul
    co
    @17
    @14
    @20
    @0
    @2
    cmul
    cB
    cC
    dp3mul10.b
    dp3mul10.c
    dpval3
    oveq1i
    cB
    cC
    dp3mul10.b
    dp3mul10.c
    dpmul10
    eqtr3i
    oveq12i
    @4
    @15
    @0
    caddc
    co
    #
    @2
    cmul
    co
    @18
    @3
    @21
    @2
    cmul
    @3
    cA
    @0
    cdc
    @21
    cA
    @0
    dp3mul10.a
    @9
    dpmul10
    cA
    @0
    dfdec10
    eqtri
    oveq1i
    @15
    @0
    @2
    @2
    cA
    @12
    @10
    mulcli
    @11
    @12
    adddiri
    eqtr2i
    3eqtr2ri
    @5
    @7
    @1
    cmul
    @19
    oveq2i
    3eqtr3ri
end

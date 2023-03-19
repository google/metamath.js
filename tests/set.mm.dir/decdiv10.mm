include "cdp.mm"
include "co.mm"
include "c1.mm"
include "cc0.mm"
include "cdc.mm"
include "cmul.mm"
include "cdiv.mm"
include "dpmul10.mm"
include "oveq1i.mm"
include "cn0.mm"
include "wcel.mm"
include "cr.mm"
include "dpcl.mm"
include "mp2an.mm"
include "recni.mm"
include "10nn.mm"
include "nncni.mm"
include "nnne0i.mm"
include "divcan4i.mm"
include "eqtr3i.mm"

theorem decdiv10
  let cA: class A
  let cB: class B
  assume dpval2.a: |- A e. NN0
  assume dpval2.b: |- B e. RR


  assert |- ( ; A B / ; 1 0 ) = ( A . B )

  proof
    cA
    cB
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
    @1
    cdiv
    co
    cA
    cB
    cdc
    #
    @1
    cdiv
    co
    @0
    @2
    @3
    @1
    cdiv
    cA
    cB
    dpval2.a
    dpval2.b
    dpmul10
    oveq1i
    @0
    @1
    @0
    cA
    cn0
    wcel
    cB
    cr
    wcel
    @0
    cr
    wcel
    dpval2.a
    dpval2.b
    cA
    cB
    dpcl
    mp2an
    recni
    @1
    10nn
    nncni
    @1
    10nn
    nnne0i
    divcan4i
    eqtr3i
end

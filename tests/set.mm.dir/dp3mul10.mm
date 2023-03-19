include "cdp2.mm"
include "cdp.mm"
include "co.mm"
include "c1.mm"
include "cc0.mm"
include "cdc.mm"
include "cmul.mm"
include "caddc.mm"
include "cr.mm"
include "wcel.mm"
include "nn0rei.mm"
include "dp2cl.mm"
include "mp2an.mm"
include "dpmul10.mm"
include "dfdec10.mm"
include "cdiv.mm"
include "10nn.mm"
include "nncni.mm"
include "nn0cni.mm"
include "mulcli.mm"
include "recni.mm"
include "nnne0i.mm"
include "divcli.mm"
include "addassi.mm"
include "oveq1i.mm"
include "df-dp2.mm"
include "oveq2i.mm"
include "3eqtr4ri.mm"
include "deccl.mm"
include "dpval2.mm"
include "eqtr4i.mm"
include "3eqtri.mm"

theorem dp3mul10
  let cA: class A
  let cB: class B
  let cC: class C
  assume dp3mul10.a: |- A e. NN0
  assume dp3mul10.b: |- B e. NN0
  assume dp3mul10.c: |- C e. RR


  assert |- ( ( A . _ B C ) x. ; 1 0 ) = ( ; A B . C )

  proof
    cA
    cB
    cC
    cdp2
    #
    cdp
    co
    c1
    cc0
    cdc
    #
    cmul
    co
    cA
    @0
    cdc
    @1
    cA
    cmul
    co
    #
    @0
    caddc
    co
    #
    cA
    cB
    cdc
    #
    cC
    cdp
    co
    #
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
    #
    dp3mul10.c
    cB
    cC
    dp2cl
    mp2an
    dpmul10
    cA
    @0
    dfdec10
    @3
    @4
    cC
    @1
    cdiv
    co
    #
    caddc
    co
    #
    @5
    @2
    cB
    caddc
    co
    #
    @7
    caddc
    co
    @2
    cB
    @7
    caddc
    co
    #
    caddc
    co
    @8
    @3
    @2
    cB
    @7
    @1
    cA
    @1
    10nn
    nncni
    #
    cA
    dp3mul10.a
    nn0cni
    mulcli
    cB
    @6
    recni
    cC
    @1
    cC
    dp3mul10.c
    recni
    @11
    @1
    10nn
    nnne0i
    divcli
    addassi
    @4
    @9
    @7
    caddc
    cA
    cB
    dfdec10
    oveq1i
    @0
    @10
    @2
    caddc
    cB
    cC
    df-dp2
    oveq2i
    3eqtr4ri
    @4
    cC
    cA
    cB
    dp3mul10.a
    dp3mul10.b
    deccl
    dp3mul10.c
    dpval2
    eqtr4i
    3eqtri
end

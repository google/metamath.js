include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cle.mm"
include "wbr.mm"
include "cmul.mm"
include "clt.mm"
include "c2.mm"
include "1nn0.mm"
include "nn0addcli.mm"
include "nn0le2msqi.mm"
include "cn0.mm"
include "wcel.mm"
include "wb.mm"
include "nn0ltp1le.mm"
include "mp2an.mm"
include "nn0mulcli.mm"
include "2nn0.mm"
include "cexp.mm"
include "nn0cni.mm"
include "ax-1cn.mm"
include "binom2i.mm"
include "addcli.mm"
include "sqvali.mm"
include "oveq1i.mm"
include "oveq12i.mm"
include "3eqtr3i.mm"
include "mulid1i.mm"
include "oveq2i.mm"
include "eqtri.mm"
include "breq1i.mm"
include "bitr4i.mm"
include "3bitr4i.mm"

theorem nn0opthlem1
  let cA: class A
  let cC: class C
  assume nn0opthlem1.1: |- A e. NN0
  assume nn0opthlem1.2: |- C e. NN0


  assert |- ( A < C <-> ( ( A x. A ) + ( 2 x. A ) ) < ( C x. C ) )

  proof
    cA
    c1
    caddc
    co
    #
    cC
    cle
    wbr
    #
    @0
    @0
    cmul
    co
    #
    cC
    cC
    cmul
    co
    #
    cle
    wbr
    #
    cA
    cC
    clt
    wbr
    #
    cA
    cA
    cmul
    co
    #
    c2
    cA
    cmul
    co
    #
    caddc
    co
    #
    @3
    clt
    wbr
    #
    @0
    cC
    cA
    c1
    nn0opthlem1.1
    1nn0
    nn0addcli
    nn0opthlem1.2
    nn0le2msqi
    cA
    cn0
    wcel
    cC
    cn0
    wcel
    @5
    @1
    wb
    nn0opthlem1.1
    nn0opthlem1.2
    cA
    cC
    nn0ltp1le
    mp2an
    @9
    @8
    c1
    caddc
    co
    #
    @3
    cle
    wbr
    #
    @4
    @8
    cn0
    wcel
    @3
    cn0
    wcel
    @9
    @11
    wb
    @6
    @7
    cA
    cA
    nn0opthlem1.1
    nn0opthlem1.1
    nn0mulcli
    c2
    cA
    2nn0
    nn0opthlem1.1
    nn0mulcli
    nn0addcli
    cC
    cC
    nn0opthlem1.2
    nn0opthlem1.2
    nn0mulcli
    @8
    @3
    nn0ltp1le
    mp2an
    @2
    @10
    @3
    cle
    @2
    @6
    c2
    cA
    c1
    cmul
    co
    #
    cmul
    co
    #
    caddc
    co
    #
    c1
    c1
    cmul
    co
    #
    caddc
    co
    #
    @10
    @0
    c2
    cexp
    co
    cA
    c2
    cexp
    co
    #
    @13
    caddc
    co
    #
    c1
    c2
    cexp
    co
    #
    caddc
    co
    @2
    @16
    cA
    c1
    cA
    nn0opthlem1.1
    nn0cni
    #
    ax-1cn
    binom2i
    @0
    cA
    c1
    @20
    ax-1cn
    addcli
    sqvali
    @18
    @14
    @19
    @15
    caddc
    @17
    @6
    @13
    caddc
    cA
    @20
    sqvali
    oveq1i
    c1
    ax-1cn
    sqvali
    oveq12i
    3eqtr3i
    @14
    @8
    @15
    c1
    caddc
    @13
    @7
    @6
    caddc
    @12
    cA
    c2
    cmul
    cA
    @20
    mulid1i
    oveq2i
    oveq2i
    c1
    ax-1cn
    mulid1i
    oveq12i
    eqtri
    breq1i
    bitr4i
    3bitr4i
end

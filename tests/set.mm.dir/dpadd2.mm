include "cdp2.mm"
include "cdp.mm"
include "co.mm"
include "caddc.mm"
include "c1.mm"
include "cc0.mm"
include "cdc.mm"
include "cdiv.mm"
include "cr.mm"
include "wcel.mm"
include "nn0rei.mm"
include "crp.mm"
include "rpre.mm"
include "ax-mp.mm"
include "dp2cl.mm"
include "mp2an.mm"
include "dpval2.mm"
include "oveq12i.mm"
include "nn0cni.mm"
include "recni.mm"
include "10nn.mm"
include "nncni.mm"
include "nnne0i.mm"
include "divcli.mm"
include "add4i.mm"
include "divdiri.mm"
include "cn0.mm"
include "wceq.mm"
include "dpval.mm"
include "3eqtr3i.mm"
include "oveq1i.mm"
include "eqtr3i.mm"
include "nn0addcli.mm"
include "eqeltrri.mm"
include "eqtr4i.mm"
include "3eqtri.mm"

theorem dpadd2
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cE: class E
  let cF: class F
  let cG: class G
  let cH: class H
  let cI: class I
  assume dpadd2.a: |- A e. NN0
  assume dpadd2.b: |- B e. RR+
  assume dpadd2.c: |- C e. NN0
  assume dpadd2.d: |- D e. RR+
  assume dpadd2.e: |- E e. NN0
  assume dpadd2.f: |- F e. RR+
  assume dpadd2.g: |- G e. NN0
  assume dpadd2.h: |- H e. NN0
  assume dpadd2.i: |- ( G + H ) = I
  assume dpadd2.1: |- ( ( A . B ) + ( C . D ) ) = ( E . F )


  assert |- ( ( G . _ A B ) + ( H . _ C D ) ) = ( I . _ E F )

  proof
    cG
    cA
    cB
    cdp2
    #
    cdp
    co
    #
    cH
    cC
    cD
    cdp2
    #
    cdp
    co
    #
    caddc
    co
    cG
    @0
    c1
    cc0
    cdc
    #
    cdiv
    co
    #
    caddc
    co
    #
    cH
    @2
    @4
    cdiv
    co
    #
    caddc
    co
    #
    caddc
    co
    cG
    cH
    caddc
    co
    #
    @5
    @7
    caddc
    co
    #
    caddc
    co
    #
    cI
    cE
    cF
    cdp2
    #
    cdp
    co
    #
    @1
    @6
    @3
    @8
    caddc
    cG
    @0
    dpadd2.g
    cA
    cr
    wcel
    cB
    cr
    wcel
    #
    @0
    cr
    wcel
    cA
    dpadd2.a
    nn0rei
    cB
    crp
    wcel
    @14
    dpadd2.b
    cB
    rpre
    ax-mp
    #
    cA
    cB
    dp2cl
    mp2an
    #
    dpval2
    cH
    @2
    dpadd2.h
    cC
    cr
    wcel
    cD
    cr
    wcel
    #
    @2
    cr
    wcel
    cC
    dpadd2.c
    nn0rei
    cD
    crp
    wcel
    @17
    dpadd2.d
    cD
    rpre
    ax-mp
    #
    cC
    cD
    dp2cl
    mp2an
    #
    dpval2
    oveq12i
    cG
    @5
    cH
    @7
    cG
    dpadd2.g
    nn0cni
    @0
    @4
    @0
    @16
    recni
    #
    @4
    10nn
    nncni
    #
    @4
    10nn
    nnne0i
    #
    divcli
    cH
    dpadd2.h
    nn0cni
    @2
    @4
    @2
    @19
    recni
    #
    @21
    @22
    divcli
    add4i
    @11
    cI
    @12
    @4
    cdiv
    co
    #
    caddc
    co
    @13
    @9
    cI
    @10
    @24
    caddc
    dpadd2.i
    @0
    @2
    caddc
    co
    #
    @4
    cdiv
    co
    @10
    @24
    @0
    @2
    @4
    @20
    @23
    @21
    @22
    divdiri
    @25
    @12
    @4
    cdiv
    cA
    cB
    cdp
    co
    #
    cC
    cD
    cdp
    co
    #
    caddc
    co
    cE
    cF
    cdp
    co
    #
    @25
    @12
    dpadd2.1
    @26
    @0
    @27
    @2
    caddc
    cA
    cn0
    wcel
    @14
    @26
    @0
    wceq
    dpadd2.a
    @15
    cA
    cB
    dpval
    mp2an
    cC
    cn0
    wcel
    @17
    @27
    @2
    wceq
    dpadd2.c
    @18
    cC
    cD
    dpval
    mp2an
    oveq12i
    cE
    cn0
    wcel
    cF
    cr
    wcel
    #
    @28
    @12
    wceq
    dpadd2.e
    cF
    crp
    wcel
    @29
    dpadd2.f
    cF
    rpre
    ax-mp
    #
    cE
    cF
    dpval
    mp2an
    3eqtr3i
    oveq1i
    eqtr3i
    oveq12i
    cI
    @12
    @9
    cI
    cn0
    dpadd2.i
    cG
    cH
    dpadd2.g
    dpadd2.h
    nn0addcli
    eqeltrri
    cE
    cr
    wcel
    @29
    @12
    cr
    wcel
    cE
    dpadd2.e
    nn0rei
    @30
    cE
    cF
    dp2cl
    mp2an
    dpval2
    eqtr4i
    3eqtri
end

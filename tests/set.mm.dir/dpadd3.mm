include "cdp2.mm"
include "cdp.mm"
include "co.mm"
include "caddc.mm"
include "cc.mm"
include "wcel.mm"
include "c1.mm"
include "cc0.mm"
include "cdc.mm"
include "wne.mm"
include "wa.mm"
include "w3a.mm"
include "cmul.mm"
include "wceq.mm"
include "cn0.mm"
include "cr.mm"
include "nn0rei.mm"
include "dp2cl.mm"
include "mp2an.mm"
include "dpcl.mm"
include "recni.mm"
include "addcli.mm"
include "10nn.mm"
include "decnncl2.mm"
include "nncni.mm"
include "nnne0i.mm"
include "pm3.2i.mm"
include "3pm3.2i.mm"
include "adddiri.mm"
include "dpmul100.mm"
include "oveq12i.mm"
include "3eqtr4i.mm"
include "eqtri.mm"
include "mulcan2.mm"
include "biimpa.mm"

theorem dpadd3
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cE: class E
  let cF: class F
  let cG: class G
  let cH: class H
  let cI: class I
  assume dpmul.a: |- A e. NN0
  assume dpmul.b: |- B e. NN0
  assume dpmul.c: |- C e. NN0
  assume dpmul.d: |- D e. NN0
  assume dpmul.e: |- E e. NN0
  assume dpmul.g: |- G e. NN0
  assume dpadd3.f: |- F e. NN0
  assume dpadd3.h: |- H e. NN0
  assume dpadd3.i: |- I e. NN0
  assume dpadd3.1: |- ( ; ; A B C + ; ; D E F ) = ; ; G H I


  assert |- ( ( A . _ B C ) + ( D . _ E F ) ) = ( G . _ H I )

  proof
    cA
    cB
    cC
    cdp2
    #
    cdp
    co
    #
    cD
    cE
    cF
    cdp2
    #
    cdp
    co
    #
    caddc
    co
    #
    cc
    wcel
    #
    cG
    cH
    cI
    cdp2
    #
    cdp
    co
    #
    cc
    wcel
    #
    c1
    cc0
    cdc
    #
    cc0
    cdc
    #
    cc
    wcel
    #
    @10
    cc0
    wne
    #
    wa
    #
    w3a
    #
    @4
    @10
    cmul
    co
    #
    @7
    @10
    cmul
    co
    #
    wceq
    #
    @4
    @7
    wceq
    #
    @5
    @8
    @13
    @1
    @3
    @1
    cA
    cn0
    wcel
    @0
    cr
    wcel
    #
    @1
    cr
    wcel
    dpmul.a
    cB
    cr
    wcel
    cC
    cr
    wcel
    @19
    cB
    dpmul.b
    nn0rei
    cC
    dpmul.c
    nn0rei
    #
    cB
    cC
    dp2cl
    mp2an
    cA
    @0
    dpcl
    mp2an
    recni
    #
    @3
    cD
    cn0
    wcel
    @2
    cr
    wcel
    #
    @3
    cr
    wcel
    dpmul.d
    cE
    cr
    wcel
    cF
    cr
    wcel
    @22
    cE
    dpmul.e
    nn0rei
    cF
    dpadd3.f
    nn0rei
    #
    cE
    cF
    dp2cl
    mp2an
    cD
    @2
    dpcl
    mp2an
    recni
    #
    addcli
    @7
    cG
    cn0
    wcel
    @6
    cr
    wcel
    #
    @7
    cr
    wcel
    dpmul.g
    cH
    cr
    wcel
    cI
    cr
    wcel
    @25
    cH
    dpadd3.h
    nn0rei
    cI
    dpadd3.i
    nn0rei
    #
    cH
    cI
    dp2cl
    mp2an
    cG
    @6
    dpcl
    mp2an
    recni
    @11
    @12
    @10
    @9
    10nn
    decnncl2
    #
    nncni
    #
    @10
    @27
    nnne0i
    pm3.2i
    3pm3.2i
    @15
    @1
    @10
    cmul
    co
    #
    @3
    @10
    cmul
    co
    #
    caddc
    co
    #
    @16
    @1
    @3
    @10
    @21
    @24
    @28
    adddiri
    cA
    cB
    cdc
    cC
    cdc
    #
    cD
    cE
    cdc
    cF
    cdc
    #
    caddc
    co
    cG
    cH
    cdc
    cI
    cdc
    @31
    @16
    dpadd3.1
    @29
    @32
    @30
    @33
    caddc
    cA
    cB
    cC
    dpmul.a
    dpmul.b
    @20
    dpmul100
    cD
    cE
    cF
    dpmul.d
    dpmul.e
    @23
    dpmul100
    oveq12i
    cG
    cH
    cI
    dpmul.g
    dpadd3.h
    @26
    dpmul100
    3eqtr4i
    eqtri
    @14
    @17
    @18
    @4
    @7
    @10
    mulcan2
    biimpa
    mp2an
end

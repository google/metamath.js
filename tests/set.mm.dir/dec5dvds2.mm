include "c5.mm"
include "cdc.mm"
include "cdvds.mm"
include "wbr.mm"
include "dec5dvds.mm"
include "caddc.mm"
include "co.mm"
include "cz.mm"
include "wcel.mm"
include "wb.mm"
include "5nn0.mm"
include "nn0zi.mm"
include "nnnn0i.mm"
include "deccl.mm"
include "dvdsadd.mm"
include "mp2an.mm"
include "cc0.mm"
include "0nn0.mm"
include "dec0h.mm"
include "eqid.mm"
include "nn0cni.mm"
include "addid2i.mm"
include "decadd.mm"
include "breq2i.mm"
include "bitri.mm"
include "mtbi.mm"

theorem dec5dvds2
  let cA: class A
  let cB: class B
  let cC: class C
  assume dec5dvds.1: |- A e. NN0
  assume dec5dvds.2: |- B e. NN
  assume dec5dvds.3: |- B < 5
  assume dec5dvds2.4: |- ( 5 + B ) = C


  assert |- -. 5 || ; A C

  proof
    c5
    cA
    cB
    cdc
    #
    cdvds
    wbr
    #
    c5
    cA
    cC
    cdc
    #
    cdvds
    wbr
    #
    cA
    cB
    dec5dvds.1
    dec5dvds.2
    dec5dvds.3
    dec5dvds
    @1
    c5
    c5
    @0
    caddc
    co
    #
    cdvds
    wbr
    #
    @3
    c5
    cz
    wcel
    @0
    cz
    wcel
    @1
    @5
    wb
    c5
    5nn0
    nn0zi
    @0
    cA
    cB
    dec5dvds.1
    cB
    dec5dvds.2
    nnnn0i
    #
    deccl
    nn0zi
    c5
    @0
    dvdsadd
    mp2an
    @4
    @2
    c5
    cdvds
    cc0
    c5
    cA
    cB
    cA
    cC
    c5
    @0
    0nn0
    5nn0
    dec5dvds.1
    @6
    c5
    5nn0
    dec0h
    @0
    eqid
    cA
    cA
    dec5dvds.1
    nn0cni
    addid2i
    dec5dvds2.4
    decadd
    breq2i
    bitri
    mtbi
end

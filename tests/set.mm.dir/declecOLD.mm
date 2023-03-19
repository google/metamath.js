include "cdc.mm"
include "deccl.mm"
include "nn0rei.mm"
include "c9.mm"
include "cle.mm"
include "wbr.mm"
include "c10.mm"
include "clt.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cz.mm"
include "wcel.mm"
include "wb.mm"
include "nn0zi.mm"
include "9nn0.mm"
include "zleltp1.mm"
include "mp2an.mm"
include "9p1e10OLD.mm"
include "breq2i.mm"
include "bitri.mm"
include "mpbi.mm"
include "decltcOLD.mm"
include "ltleii.mm"

theorem declecOLD
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  assume decleOLD.1: |- A e. NN0
  assume decleOLD.2: |- B e. NN0
  assume decleOLD.3: |- C e. NN0
  assume declecOLD.4: |- D e. NN0
  assume declecOLD.5: |- C <_ 9
  assume declecOLD.6: |- A < B


  assert |- ; A C <_ ; B D

  proof
    cA
    cC
    cdc
    #
    cB
    cD
    cdc
    #
    @0
    cA
    cC
    decleOLD.1
    decleOLD.3
    deccl
    nn0rei
    @1
    cB
    cD
    decleOLD.2
    declecOLD.4
    deccl
    nn0rei
    cA
    cB
    cC
    cD
    decleOLD.1
    decleOLD.2
    decleOLD.3
    declecOLD.4
    cC
    c9
    cle
    wbr
    #
    cC
    c10
    clt
    wbr
    #
    declecOLD.5
    @2
    cC
    c9
    c1
    caddc
    co
    #
    clt
    wbr
    #
    @3
    cC
    cz
    wcel
    c9
    cz
    wcel
    @2
    @5
    wb
    cC
    decleOLD.3
    nn0zi
    c9
    9nn0
    nn0zi
    cC
    c9
    zleltp1
    mp2an
    @4
    c10
    cC
    clt
    9p1e10OLD
    breq2i
    bitri
    mpbi
    declecOLD.6
    decltcOLD
    ltleii
end

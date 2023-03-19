include "c2.mm"
include "cdc.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cdvds.mm"
include "wbr.mm"
include "wn.mm"
include "cc0.mm"
include "cmul.mm"
include "c5.mm"
include "cz.mm"
include "wcel.mm"
include "5nn0.mm"
include "nn0zi.mm"
include "2z.mm"
include "dvdsmul2.mm"
include "mp2an.mm"
include "5t2e10.mm"
include "breqtri.mm"
include "wi.mm"
include "10nn0.mm"
include "dvdsmultr1.mm"
include "mp3an.mm"
include "ax-mp.mm"
include "wa.mm"
include "nn0mulcli.mm"
include "cn0.mm"
include "2nn0.mm"
include "eqeltrri.mm"
include "dvds2add.mm"
include "dfdec10.mm"
include "breqtrri.mm"
include "cn.mm"
include "clt.mm"
include "deccl.mm"
include "2nn.mm"
include "1lt2.mm"
include "ndvdsp1.mm"
include "eqcomi.mm"
include "eqid.mm"
include "decsuc.mm"
include "breq2i.mm"
include "mtbi.mm"

theorem dec2dvds
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  assume dec2dvds.1: |- A e. NN0
  assume dec2dvds.2: |- B e. NN0
  assume dec2dvds.3: |- ( B x. 2 ) = C
  assume dec2dvds.4: |- D = ( C + 1 )


  assert |- -. 2 || ; A D

  proof
    c2
    cA
    cC
    cdc
    #
    c1
    caddc
    co
    #
    cdvds
    wbr
    #
    c2
    cA
    cD
    cdc
    #
    cdvds
    wbr
    c2
    @0
    cdvds
    wbr
    #
    @2
    wn
    #
    c2
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
    #
    @0
    cdvds
    c2
    @7
    cdvds
    wbr
    #
    c2
    cC
    cdvds
    wbr
    #
    c2
    @8
    cdvds
    wbr
    #
    c2
    @6
    cdvds
    wbr
    #
    @9
    c2
    c5
    c2
    cmul
    co
    #
    @6
    cdvds
    c5
    cz
    wcel
    c2
    cz
    wcel
    #
    c2
    @13
    cdvds
    wbr
    c5
    5nn0
    nn0zi
    2z
    c5
    c2
    dvdsmul2
    mp2an
    5t2e10
    breqtri
    @14
    @6
    cz
    wcel
    cA
    cz
    wcel
    @12
    @9
    wi
    2z
    @6
    10nn0
    nn0zi
    cA
    dec2dvds.1
    nn0zi
    c2
    @6
    cA
    dvdsmultr1
    mp3an
    ax-mp
    c2
    cB
    c2
    cmul
    co
    #
    cC
    cdvds
    cB
    cz
    wcel
    @14
    c2
    @15
    cdvds
    wbr
    cB
    dec2dvds.2
    nn0zi
    2z
    cB
    c2
    dvdsmul2
    mp2an
    dec2dvds.3
    breqtri
    @14
    @7
    cz
    wcel
    cC
    cz
    wcel
    @9
    @10
    wa
    @11
    wi
    2z
    @7
    @6
    cA
    10nn0
    dec2dvds.1
    nn0mulcli
    nn0zi
    cC
    @15
    cC
    cn0
    dec2dvds.3
    cB
    c2
    dec2dvds.2
    2nn0
    nn0mulcli
    eqeltrri
    #
    nn0zi
    c2
    @7
    cC
    dvds2add
    mp3an
    mp2an
    cA
    cC
    dfdec10
    breqtrri
    @0
    cz
    wcel
    c2
    cn
    wcel
    c1
    c2
    clt
    wbr
    @4
    @5
    wi
    @0
    cA
    cC
    dec2dvds.1
    @16
    deccl
    nn0zi
    2nn
    1lt2
    c2
    @0
    ndvdsp1
    mp3an
    ax-mp
    @1
    @3
    c2
    cdvds
    cA
    cC
    cD
    @0
    dec2dvds.1
    @16
    cD
    cC
    c1
    caddc
    co
    dec2dvds.4
    eqcomi
    @0
    eqid
    decsuc
    breq2i
    mtbi
end

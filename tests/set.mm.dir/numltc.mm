include "cmul.mm"
include "co.mm"
include "caddc.mm"
include "clt.mm"
include "wbr.mm"
include "cle.mm"
include "c1.mm"
include "numlt.mm"
include "nnrei.mm"
include "recni.mm"
include "nn0rei.mm"
include "ax-1cn.mm"
include "adddii.mm"
include "mulid1i.mm"
include "oveq2i.mm"
include "eqtri.mm"
include "breqtrri.mm"
include "cn0.mm"
include "wcel.mm"
include "wb.mm"
include "nn0ltp1le.mm"
include "mp2an.mm"
include "mpbi.mm"
include "cc0.mm"
include "nngt0i.mm"
include "cr.mm"
include "peano2re.mm"
include "ax-mp.mm"
include "lemul2i.mm"
include "remulcli.mm"
include "readdcli.mm"
include "ltletri.mm"
include "nn0addge1i.mm"

theorem numltc
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cT: class T
  assume numlt.1: |- T e. NN
  assume numlt.2: |- A e. NN0
  assume numlt.3: |- B e. NN0
  assume numltc.3: |- C e. NN0
  assume numltc.4: |- D e. NN0
  assume numltc.5: |- C < T
  assume numltc.6: |- A < B


  assert |- ( ( T x. A ) + C ) < ( ( T x. B ) + D )

  proof
    cT
    cA
    cmul
    co
    #
    cC
    caddc
    co
    #
    cT
    cB
    cmul
    co
    #
    clt
    wbr
    #
    @2
    @2
    cD
    caddc
    co
    #
    cle
    wbr
    @1
    @4
    clt
    wbr
    @1
    cT
    cA
    c1
    caddc
    co
    #
    cmul
    co
    #
    clt
    wbr
    @6
    @2
    cle
    wbr
    #
    @3
    @1
    @0
    cT
    caddc
    co
    #
    @6
    clt
    cA
    cC
    cT
    cT
    numlt.1
    numlt.2
    numltc.3
    numlt.1
    numltc.5
    numlt
    @6
    @0
    cT
    c1
    cmul
    co
    #
    caddc
    co
    @8
    cT
    cA
    c1
    cT
    cT
    numlt.1
    nnrei
    #
    recni
    #
    cA
    cA
    numlt.2
    nn0rei
    #
    recni
    ax-1cn
    adddii
    @9
    cT
    @0
    caddc
    cT
    @11
    mulid1i
    oveq2i
    eqtri
    breqtrri
    @5
    cB
    cle
    wbr
    #
    @7
    cA
    cB
    clt
    wbr
    #
    @13
    numltc.6
    cA
    cn0
    wcel
    cB
    cn0
    wcel
    @14
    @13
    wb
    numlt.2
    numlt.3
    cA
    cB
    nn0ltp1le
    mp2an
    mpbi
    cc0
    cT
    clt
    wbr
    @13
    @7
    wb
    cT
    numlt.1
    nngt0i
    @5
    cB
    cT
    cA
    cr
    wcel
    @5
    cr
    wcel
    @12
    cA
    peano2re
    ax-mp
    #
    cB
    numlt.3
    nn0rei
    #
    @10
    lemul2i
    ax-mp
    mpbi
    @1
    @6
    @2
    @0
    cC
    cT
    cA
    @10
    @12
    remulcli
    cC
    numltc.3
    nn0rei
    readdcli
    #
    cT
    @5
    @10
    @15
    remulcli
    cT
    cB
    @10
    @16
    remulcli
    #
    ltletri
    mp2an
    @2
    cD
    @18
    numltc.4
    nn0addge1i
    @1
    @2
    @4
    @17
    @18
    @2
    cD
    @18
    cD
    numltc.4
    nn0rei
    readdcli
    ltletri
    mp2an
end

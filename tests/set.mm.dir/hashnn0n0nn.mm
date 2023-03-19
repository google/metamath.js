include "chash.mm"
include "cfv.mm"
include "wceq.mm"
include "wcel.mm"
include "wa.mm"
include "cn0.mm"
include "cn.mm"
include "wi.mm"
include "c1.mm"
include "cle.mm"
include "wbr.mm"
include "c0.mm"
include "wne.mm"
include "ne0i.mm"
include "hashge1.mm"
include "sylan2.mm"
include "cc0.mm"
include "simpr.mm"
include "clt.mm"
include "wn.mm"
include "0lt1.mm"
include "0re.mm"
include "1re.mm"
include "ltnlei.mm"
include "mpbi.mm"
include "breq2.mm"
include "mtbiri.mm"
include "necon2ai.mm"
include "adantr.mm"
include "elnnne0.mm"
include "sylanbrc.mm"
include "ex.mm"
include "syl.mm"
include "impancom.mm"
include "com12.mm"
include "eleq1.mm"
include "anbi2d.mm"
include "imbi12d.mm"
include "syl5ib.mm"
include "imp.mm"
include "impcom.mm"

theorem hashnn0n0nn
  let cN: class N
  let cV: class V
  let cW: class W
  let cY: class Y


  assert |- ( ( ( V e. W /\ Y e. NN0 ) /\ ( ( # ` V ) = Y /\ N e. V ) ) -> Y e. NN )

  proof
    cV
    chash
    cfv
    #
    cY
    wceq
    #
    cN
    cV
    wcel
    #
    wa
    cV
    cW
    wcel
    #
    cY
    cn0
    wcel
    #
    wa
    #
    cY
    cn
    wcel
    #
    @1
    @2
    @5
    @6
    wi
    #
    @2
    @3
    @0
    cn0
    wcel
    #
    wa
    #
    @0
    cn
    wcel
    #
    wi
    @1
    @7
    @9
    @2
    @10
    @3
    @2
    @8
    @10
    @3
    @2
    wa
    c1
    @0
    cle
    wbr
    #
    @8
    @10
    wi
    @2
    @3
    cV
    c0
    wne
    @11
    cV
    cN
    ne0i
    cV
    cW
    hashge1
    sylan2
    @11
    @8
    @10
    @11
    @8
    wa
    @8
    @0
    cc0
    wne
    #
    @10
    @11
    @8
    simpr
    @11
    @12
    @8
    @11
    @0
    cc0
    @0
    cc0
    wceq
    @11
    c1
    cc0
    cle
    wbr
    #
    cc0
    c1
    clt
    wbr
    @13
    wn
    0lt1
    cc0
    c1
    0re
    1re
    ltnlei
    mpbi
    @0
    cc0
    c1
    cle
    breq2
    mtbiri
    necon2ai
    adantr
    @0
    elnnne0
    sylanbrc
    ex
    syl
    impancom
    com12
    @1
    @9
    @5
    @10
    @6
    @1
    @8
    @4
    @3
    @0
    cY
    cn0
    eleq1
    anbi2d
    @0
    cY
    cn
    eleq1
    imbi12d
    syl5ib
    imp
    impcom
end

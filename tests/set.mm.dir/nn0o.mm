include "c1.mm"
include "wceq.mm"
include "c2.mm"
include "clt.mm"
include "wbr.mm"
include "wo.mm"
include "cn0.mm"
include "wcel.mm"
include "caddc.mm"
include "co.mm"
include "cdiv.mm"
include "wa.mm"
include "cmin.mm"
include "nn0o1gt2.mm"
include "wi.mm"
include "cc0.mm"
include "1m1e0.mm"
include "oveq1i.mm"
include "2cn.mm"
include "2ne0.mm"
include "div0i.mm"
include "eqtri.mm"
include "0nn0.mm"
include "eqeltri.mm"
include "wb.mm"
include "oveq1.mm"
include "oveq1d.mm"
include "eleq1d.mm"
include "adantr.mm"
include "mpbiri.mm"
include "ex.mm"
include "cuz.mm"
include "cfv.mm"
include "cn.mm"
include "cz.mm"
include "cle.mm"
include "2z.mm"
include "a1i.mm"
include "nn0z.mm"
include "ad2antrl.mm"
include "cr.mm"
include "2re.mm"
include "nn0re.mm"
include "ltle.mm"
include "sylancr.mm"
include "impcom.mm"
include "eluz2.mm"
include "syl3anbrc.mm"
include "simprr.mm"
include "jca.mm"
include "nno.mm"
include "nnnn0.mm"
include "3syl.mm"
include "jaoi.mm"
include "mpcom.mm"

theorem nn0o
  let cN: class N


  assert |- ( ( N e. NN0 /\ ( ( N + 1 ) / 2 ) e. NN0 ) -> ( ( N - 1 ) / 2 ) e. NN0 )

  proof
    cN
    c1
    wceq
    #
    c2
    cN
    clt
    wbr
    #
    wo
    cN
    cn0
    wcel
    #
    cN
    c1
    caddc
    co
    c2
    cdiv
    co
    cn0
    wcel
    #
    wa
    #
    cN
    c1
    cmin
    co
    #
    c2
    cdiv
    co
    #
    cn0
    wcel
    #
    cN
    nn0o1gt2
    @0
    @4
    @7
    wi
    @1
    @0
    @4
    @7
    @0
    @4
    wa
    @7
    c1
    c1
    cmin
    co
    #
    c2
    cdiv
    co
    #
    cn0
    wcel
    #
    @9
    cc0
    cn0
    @9
    cc0
    c2
    cdiv
    co
    cc0
    @8
    cc0
    c2
    cdiv
    1m1e0
    oveq1i
    c2
    2cn
    2ne0
    div0i
    eqtri
    0nn0
    eqeltri
    @0
    @7
    @10
    wb
    @4
    @0
    @6
    @9
    cn0
    @0
    @5
    @8
    c2
    cdiv
    cN
    c1
    c1
    cmin
    oveq1
    oveq1d
    eleq1d
    adantr
    mpbiri
    ex
    @1
    @4
    @7
    @1
    @4
    wa
    #
    cN
    c2
    cuz
    cfv
    wcel
    #
    @3
    wa
    @6
    cn
    wcel
    @7
    @11
    @12
    @3
    @11
    c2
    cz
    wcel
    #
    cN
    cz
    wcel
    #
    c2
    cN
    cle
    wbr
    #
    @12
    @13
    @11
    2z
    a1i
    @2
    @14
    @1
    @3
    cN
    nn0z
    ad2antrl
    @4
    @1
    @15
    @2
    @1
    @15
    wi
    #
    @3
    @2
    c2
    cr
    wcel
    cN
    cr
    wcel
    @16
    2re
    cN
    nn0re
    c2
    cN
    ltle
    sylancr
    adantr
    impcom
    c2
    cN
    eluz2
    syl3anbrc
    @1
    @2
    @3
    simprr
    jca
    cN
    nno
    @6
    nnnn0
    3syl
    ex
    jaoi
    mpcom
end

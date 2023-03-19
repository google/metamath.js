include "cr.mm"
include "wcel.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cdiv.mm"
include "clt.mm"
include "cmul.mm"
include "ltp1.mm"
include "cc.mm"
include "wceq.mm"
include "recn.mm"
include "ax-1cn.mm"
include "addcom.mm"
include "sylancl.mm"
include "breqtrd.mm"
include "adantr.mm"
include "1re.mm"
include "readdcl.mm"
include "mpan.mm"
include "recnd.mm"
include "0lt1.mm"
include "addgtge0.mm"
include "mpanr1.mm"
include "mpanl1.mm"
include "gt0ne0d.mm"
include "divcan1d.mm"
include "mulid2d.mm"
include "3brtr4d.mm"
include "wb.mm"
include "simpl.mm"
include "redivcld.mm"
include "ltmul1.mm"
include "mp3an2.mm"
include "syl12anc.mm"
include "mpbird.mm"

theorem recp1lt1
  let cA: class A


  assert |- ( ( A e. RR /\ 0 <_ A ) -> ( A / ( 1 + A ) ) < 1 )

  proof
    cA
    cr
    wcel
    #
    cc0
    cA
    cle
    wbr
    #
    wa
    #
    cA
    c1
    cA
    caddc
    co
    #
    cdiv
    co
    #
    c1
    clt
    wbr
    #
    @4
    @3
    cmul
    co
    #
    c1
    @3
    cmul
    co
    #
    clt
    wbr
    #
    @2
    cA
    @3
    @6
    @7
    clt
    @0
    cA
    @3
    clt
    wbr
    @1
    @0
    cA
    cA
    c1
    caddc
    co
    #
    @3
    clt
    cA
    ltp1
    @0
    cA
    cc
    wcel
    #
    c1
    cc
    wcel
    @9
    @3
    wceq
    cA
    recn
    #
    ax-1cn
    cA
    c1
    addcom
    sylancl
    breqtrd
    adantr
    @2
    cA
    @3
    @0
    @10
    @1
    @11
    adantr
    @2
    @3
    @0
    @3
    cr
    wcel
    #
    @1
    c1
    cr
    wcel
    #
    @0
    @12
    1re
    c1
    cA
    readdcl
    mpan
    #
    adantr
    #
    recnd
    @2
    @3
    @13
    @0
    @1
    cc0
    @3
    clt
    wbr
    #
    1re
    @13
    @0
    wa
    cc0
    c1
    clt
    wbr
    @1
    @16
    0lt1
    c1
    cA
    addgtge0
    mpanr1
    mpanl1
    #
    gt0ne0d
    #
    divcan1d
    @0
    @7
    @3
    wceq
    @1
    @0
    @3
    @0
    @3
    @14
    recnd
    mulid2d
    adantr
    3brtr4d
    @2
    @4
    cr
    wcel
    #
    @12
    @16
    @5
    @8
    wb
    #
    @2
    cA
    @3
    @0
    @1
    simpl
    @15
    @18
    redivcld
    @15
    @17
    @19
    @13
    @12
    @16
    wa
    @20
    1re
    @4
    c1
    @3
    ltmul1
    mp3an2
    syl12anc
    mpbird
end

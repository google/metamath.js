include "crp.mm"
include "wcel.mm"
include "cr.mm"
include "c1.mm"
include "clt.mm"
include "wbr.mm"
include "w3a.mm"
include "cdiv.mm"
include "co.mm"
include "cv.mm"
include "cexp.mm"
include "cn.mm"
include "wrex.mm"
include "rpre.mm"
include "rpne0.mm"
include "rereccld.mm"
include "expnbnd.mm"
include "syl3an1.mm"
include "wa.mm"
include "cc0.mm"
include "wb.mm"
include "rpregt0.mm"
include "3ad2ant1.mm"
include "adantr.mm"
include "cn0.mm"
include "nnnn0.mm"
include "reexpcl.mm"
include "sylan2.mm"
include "adantlr.mm"
include "cz.mm"
include "simpll.mm"
include "nnz.mm"
include "adantl.mm"
include "0lt1.mm"
include "wi.mm"
include "0re.mm"
include "1re.mm"
include "lttr.mm"
include "mp3an12.mm"
include "mpani.mm"
include "imp.mm"
include "expgt0.mm"
include "syl3anc.mm"
include "jca.mm"
include "3adantl1.mm"
include "ltrec1.mm"
include "syl2anc.mm"
include "rexbidva.mm"
include "mpbid.mm"

theorem expnlbnd
  let cA: class A
  let cB: class B
  let vk: setvar k
  let vj: setvar j

  disjoint A k
  disjoint B k
  disjoint j k
  disjoint A j
  disjoint B j
  assert |- ( ( A e. RR+ /\ B e. RR /\ 1 < B ) -> E. k e. NN ( 1 / ( B ^ k ) ) < A )

  proof
    cA
    crp
    wcel
    #
    cB
    cr
    wcel
    #
    c1
    cB
    clt
    wbr
    #
    w3a
    #
    c1
    cA
    cdiv
    co
    #
    cB
    vk
    cv
    #
    cexp
    co
    #
    clt
    wbr
    #
    vk
    cn
    wrex
    #
    c1
    @6
    cdiv
    co
    cA
    clt
    wbr
    #
    vk
    cn
    wrex
    @0
    @4
    cr
    wcel
    @1
    @2
    @8
    @0
    cA
    cA
    rpre
    cA
    rpne0
    rereccld
    @4
    cB
    vk
    expnbnd
    syl3an1
    @3
    @7
    @9
    vk
    cn
    @3
    @5
    cn
    wcel
    #
    wa
    cA
    cr
    wcel
    cc0
    cA
    clt
    wbr
    wa
    #
    @6
    cr
    wcel
    #
    cc0
    @6
    clt
    wbr
    #
    wa
    #
    @7
    @9
    wb
    @3
    @11
    @10
    @0
    @1
    @11
    @2
    cA
    rpregt0
    3ad2ant1
    adantr
    @1
    @2
    @10
    @14
    @0
    @1
    @2
    wa
    #
    @10
    wa
    #
    @12
    @13
    @1
    @10
    @12
    @2
    @10
    @1
    @5
    cn0
    wcel
    @12
    @5
    nnnn0
    cB
    @5
    reexpcl
    sylan2
    adantlr
    @16
    @1
    @5
    cz
    wcel
    #
    cc0
    cB
    clt
    wbr
    #
    @13
    @1
    @2
    @10
    simpll
    @10
    @17
    @15
    @5
    nnz
    adantl
    @15
    @18
    @10
    @1
    @2
    @18
    @1
    cc0
    c1
    clt
    wbr
    #
    @2
    @18
    0lt1
    cc0
    cr
    wcel
    c1
    cr
    wcel
    @1
    @19
    @2
    wa
    @18
    wi
    0re
    1re
    cc0
    c1
    cB
    lttr
    mp3an12
    mpani
    imp
    adantr
    cB
    @5
    expgt0
    syl3anc
    jca
    3adantl1
    cA
    @6
    ltrec1
    syl2anc
    rexbidva
    mpbid
end

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
include "cmul.mm"
include "simprl.mm"
include "peano2re.mm"
include "ad2antrl.mm"
include "simpll.mm"
include "wne.mm"
include "clt.mm"
include "ltp1.mm"
include "wi.mm"
include "0re.mm"
include "lelttr.mm"
include "mp3an1.mm"
include "mpdan.mm"
include "mpan2d.mm"
include "imp.mm"
include "gt0ne0d.mm"
include "adantl.mm"
include "redivcld.mm"
include "adantr.mm"
include "jca.mm"
include "divge0.mm"
include "sylan2.mm"
include "lep1.mm"
include "lemul2a.mm"
include "syl31anc.mm"
include "cc.mm"
include "recn.mm"
include "ad2antrr.mm"
include "recnd.mm"
include "divcan1d.mm"
include "breqtrd.mm"

theorem ledivp1
  let cA: class A
  let cB: class B


  assert |- ( ( ( A e. RR /\ 0 <_ A ) /\ ( B e. RR /\ 0 <_ B ) ) -> ( ( A / ( B + 1 ) ) x. B ) <_ A )

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
    cB
    cr
    wcel
    #
    cc0
    cB
    cle
    wbr
    #
    wa
    #
    wa
    #
    cA
    cB
    c1
    caddc
    co
    #
    cdiv
    co
    #
    cB
    cmul
    co
    #
    @8
    @7
    cmul
    co
    #
    cA
    cle
    @6
    @3
    @7
    cr
    wcel
    #
    @8
    cr
    wcel
    #
    cc0
    @8
    cle
    wbr
    #
    wa
    cB
    @7
    cle
    wbr
    #
    @9
    @10
    cle
    wbr
    @2
    @3
    @4
    simprl
    @3
    @11
    @2
    @4
    cB
    peano2re
    #
    ad2antrl
    #
    @6
    @12
    @13
    @6
    cA
    @7
    @0
    @1
    @5
    simpll
    @16
    @5
    @7
    cc0
    wne
    @2
    @5
    @7
    @3
    @4
    cc0
    @7
    clt
    wbr
    #
    @3
    @4
    cB
    @7
    clt
    wbr
    #
    @17
    cB
    ltp1
    @3
    @11
    @4
    @18
    wa
    @17
    wi
    #
    @15
    cc0
    cr
    wcel
    @3
    @11
    @19
    0re
    cc0
    cB
    @7
    lelttr
    mp3an1
    mpdan
    mpan2d
    imp
    #
    gt0ne0d
    adantl
    #
    redivcld
    @5
    @2
    @11
    @17
    wa
    @13
    @5
    @11
    @17
    @3
    @11
    @4
    @15
    adantr
    @20
    jca
    cA
    @7
    divge0
    sylan2
    jca
    @3
    @14
    @2
    @4
    cB
    lep1
    ad2antrl
    cB
    @7
    @8
    lemul2a
    syl31anc
    @6
    cA
    @7
    @0
    cA
    cc
    wcel
    @1
    @5
    cA
    recn
    ad2antrr
    @3
    @7
    cc
    wcel
    @2
    @4
    @3
    @7
    @15
    recnd
    ad2antrl
    @21
    divcan1d
    breqtrd
end

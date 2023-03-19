include "cr.mm"
include "wcel.mm"
include "cc0.mm"
include "wne.mm"
include "wa.mm"
include "clt.mm"
include "wbr.mm"
include "cneg.mm"
include "wn.mm"
include "crp.mm"
include "wo.mm"
include "cle.mm"
include "wi.mm"
include "0re.mm"
include "ltle.mm"
include "mpan.mm"
include "imp.mm"
include "olcd.mm"
include "renegcl.mm"
include "pm2.24d.mm"
include "adantr.mm"
include "wb.mm"
include "ltlen.mm"
include "biimprd.mm"
include "expcomd.mm"
include "jaod.mm"
include "simpl.mm"
include "jctild.mm"
include "impbid2.mm"
include "lenlt.mm"
include "lt0neg1.mm"
include "notbid.mm"
include "bitrd.mm"
include "orbi2d.mm"
include "ianor.mm"
include "syl6bbr.mm"
include "elrp.mm"
include "notbii.mm"
include "3bitr4g.mm"

theorem rpneg
  let cA: class A


  assert |- ( ( A e. RR /\ A =/= 0 ) -> ( A e. RR+ <-> -. -u A e. RR+ ) )

  proof
    cA
    cr
    wcel
    #
    cA
    cc0
    wne
    #
    wa
    #
    @0
    cc0
    cA
    clt
    wbr
    #
    wa
    #
    cA
    cneg
    #
    cr
    wcel
    #
    cc0
    @5
    clt
    wbr
    #
    wa
    #
    wn
    #
    cA
    crp
    wcel
    @5
    crp
    wcel
    #
    wn
    @2
    @4
    @6
    wn
    #
    @7
    wn
    #
    wo
    #
    @9
    @2
    @4
    @11
    cc0
    cA
    cle
    wbr
    #
    wo
    #
    @13
    @2
    @4
    @15
    @4
    @14
    @11
    @0
    @3
    @14
    cc0
    cr
    wcel
    #
    @0
    @3
    @14
    wi
    0re
    cc0
    cA
    ltle
    mpan
    imp
    olcd
    @2
    @15
    @3
    @0
    @2
    @11
    @3
    @14
    @0
    @11
    @3
    wi
    @1
    @0
    @6
    @3
    cA
    renegcl
    pm2.24d
    adantr
    @0
    @1
    @14
    @3
    wi
    @0
    @14
    @1
    @3
    @0
    @3
    @14
    @1
    wa
    #
    @16
    @0
    @3
    @17
    wb
    0re
    cc0
    cA
    ltlen
    mpan
    biimprd
    expcomd
    imp
    jaod
    @0
    @1
    simpl
    jctild
    impbid2
    @2
    @14
    @12
    @11
    @0
    @14
    @12
    wb
    @1
    @0
    @14
    cA
    cc0
    clt
    wbr
    #
    wn
    #
    @12
    @16
    @0
    @14
    @19
    wb
    0re
    cc0
    cA
    lenlt
    mpan
    @0
    @18
    @7
    cA
    lt0neg1
    notbid
    bitrd
    adantr
    orbi2d
    bitrd
    @6
    @7
    ianor
    syl6bbr
    cA
    elrp
    @10
    @8
    @5
    elrp
    notbii
    3bitr4g
end

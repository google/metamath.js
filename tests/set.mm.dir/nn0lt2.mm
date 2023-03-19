include "cn0.mm"
include "wcel.mm"
include "c2.mm"
include "clt.mm"
include "wbr.mm"
include "wa.mm"
include "cc0.mm"
include "wceq.mm"
include "c1.mm"
include "wo.mm"
include "wi.mm"
include "olc.mm"
include "a1d.mm"
include "wne.mm"
include "cle.mm"
include "cmin.mm"
include "co.mm"
include "cz.mm"
include "wb.mm"
include "nn0z.mm"
include "2z.mm"
include "zltlem1.mm"
include "sylancl.mm"
include "2m1e1.mm"
include "breq2i.mm"
include "syl6bb.mm"
include "necom.mm"
include "cr.mm"
include "nn0re.mm"
include "1re.mm"
include "ltlen.mm"
include "nn0lt10b.mm"
include "biimpa.mm"
include "orcd.mm"
include "ex.mm"
include "sylbird.mm"
include "expd.mm"
include "syl7bi.mm"
include "sylbid.mm"
include "imp.mm"
include "com12.mm"
include "pm2.61ine.mm"

theorem nn0lt2
  let cN: class N


  assert |- ( ( N e. NN0 /\ N < 2 ) -> ( N = 0 \/ N = 1 ) )

  proof
    cN
    cn0
    wcel
    #
    cN
    c2
    clt
    wbr
    #
    wa
    #
    cN
    cc0
    wceq
    #
    cN
    c1
    wceq
    #
    wo
    #
    wi
    cN
    c1
    @4
    @5
    @2
    @4
    @3
    olc
    a1d
    @2
    cN
    c1
    wne
    #
    @5
    @0
    @1
    @6
    @5
    wi
    #
    @0
    @1
    cN
    c1
    cle
    wbr
    #
    @7
    @0
    @1
    cN
    c2
    c1
    cmin
    co
    #
    cle
    wbr
    #
    @8
    @0
    cN
    cz
    wcel
    c2
    cz
    wcel
    @1
    @10
    wb
    cN
    nn0z
    2z
    cN
    c2
    zltlem1
    sylancl
    @9
    c1
    cN
    cle
    2m1e1
    breq2i
    syl6bb
    @6
    c1
    cN
    wne
    #
    @0
    @8
    @5
    cN
    c1
    necom
    @0
    @8
    @11
    @5
    @0
    @8
    @11
    wa
    #
    cN
    c1
    clt
    wbr
    #
    @5
    @0
    cN
    cr
    wcel
    c1
    cr
    wcel
    @13
    @12
    wb
    cN
    nn0re
    1re
    cN
    c1
    ltlen
    sylancl
    @0
    @13
    @5
    @0
    @13
    wa
    @3
    @4
    @0
    @13
    @3
    cN
    nn0lt10b
    biimpa
    orcd
    ex
    sylbird
    expd
    syl7bi
    sylbid
    imp
    com12
    pm2.61ine
end

include "cn0.mm"
include "wcel.mm"
include "c2.mm"
include "cexp.mm"
include "co.mm"
include "c1.mm"
include "wceq.mm"
include "wne.mm"
include "clt.mm"
include "wbr.mm"
include "wo.mm"
include "nn0re.mm"
include "1red.mm"
include "lttri2d.mm"
include "wa.mm"
include "cc0.mm"
include "nn0lt10b.mm"
include "biimpa.mm"
include "sq0id.mm"
include "0ne1.mm"
include "a1i.mm"
include "eqnetrd.mm"
include "sq1.mm"
include "cle.mm"
include "0le1.mm"
include "nn0ge0.mm"
include "lt2sqd.mm"
include "syl5eqbrr.mm"
include "gtned.mm"
include "jaodan.mm"
include "ex.mm"
include "sylbid.mm"
include "necon4d.mm"
include "imp.mm"

theorem nn0sqeq1
  let cN: class N


  assert |- ( ( N e. NN0 /\ ( N ^ 2 ) = 1 ) -> N = 1 )

  proof
    cN
    cn0
    wcel
    #
    cN
    c2
    cexp
    co
    #
    c1
    wceq
    cN
    c1
    wceq
    @0
    cN
    c1
    @1
    c1
    @0
    cN
    c1
    wne
    cN
    c1
    clt
    wbr
    #
    c1
    cN
    clt
    wbr
    #
    wo
    #
    @1
    c1
    wne
    #
    @0
    cN
    c1
    cN
    nn0re
    #
    @0
    1red
    #
    lttri2d
    @0
    @4
    @5
    @0
    @2
    @5
    @3
    @0
    @2
    wa
    #
    @1
    cc0
    c1
    @8
    cN
    @0
    @2
    cN
    cc0
    wceq
    cN
    nn0lt10b
    biimpa
    sq0id
    cc0
    c1
    wne
    @8
    0ne1
    a1i
    eqnetrd
    @0
    @3
    wa
    #
    c1
    @1
    @9
    1red
    @9
    c1
    c1
    c2
    cexp
    co
    #
    @1
    clt
    sq1
    @0
    @3
    @10
    @1
    clt
    wbr
    @0
    c1
    cN
    @7
    @6
    cc0
    c1
    cle
    wbr
    @0
    0le1
    a1i
    cN
    nn0ge0
    lt2sqd
    biimpa
    syl5eqbrr
    gtned
    jaodan
    ex
    sylbid
    necon4d
    imp
end

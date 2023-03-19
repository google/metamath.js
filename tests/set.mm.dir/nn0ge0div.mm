include "cn0.mm"
include "wcel.mm"
include "cn.mm"
include "wa.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "cdiv.mm"
include "co.mm"
include "nn0ge0.mm"
include "adantr.mm"
include "cr.mm"
include "clt.mm"
include "w3a.mm"
include "wb.mm"
include "cz.mm"
include "elnnz.mm"
include "nn0re.mm"
include "zre.mm"
include "ad2antrl.mm"
include "simprr.mm"
include "3jca.mm"
include "sylan2b.mm"
include "ge0div.mm"
include "syl.mm"
include "mpbid.mm"

theorem nn0ge0div
  let cK: class K
  let cL: class L


  assert |- ( ( K e. NN0 /\ L e. NN ) -> 0 <_ ( K / L ) )

  proof
    cK
    cn0
    wcel
    #
    cL
    cn
    wcel
    #
    wa
    #
    cc0
    cK
    cle
    wbr
    #
    cc0
    cK
    cL
    cdiv
    co
    cle
    wbr
    #
    @0
    @3
    @1
    cK
    nn0ge0
    adantr
    @2
    cK
    cr
    wcel
    #
    cL
    cr
    wcel
    #
    cc0
    cL
    clt
    wbr
    #
    w3a
    #
    @3
    @4
    wb
    @1
    @0
    cL
    cz
    wcel
    #
    @7
    wa
    #
    @8
    cL
    elnnz
    @0
    @10
    wa
    @5
    @6
    @7
    @0
    @5
    @10
    cK
    nn0re
    adantr
    @9
    @6
    @0
    @7
    cL
    zre
    ad2antrl
    @0
    @9
    @7
    simprr
    3jca
    sylan2b
    cK
    cL
    ge0div
    syl
    mpbid
end

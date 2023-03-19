include "cn0.mm"
include "wcel.mm"
include "cz.mm"
include "cc0.mm"
include "clt.mm"
include "wbr.mm"
include "wo.mm"
include "cfz.mm"
include "co.mm"
include "wn.mm"
include "cbc.mm"
include "wceq.mm"
include "wa.mm"
include "wi.mm"
include "cle.mm"
include "elfzle1.mm"
include "cr.mm"
include "wb.mm"
include "0re.mm"
include "elfzelz.mm"
include "zred.mm"
include "lenlt.mm"
include "sylancr.mm"
include "mpbid.mm"
include "adantl.mm"
include "elfzle2.mm"
include "nn0re.mm"
include "syl2anr.mm"
include "ioran.mm"
include "sylanbrc.mm"
include "ex.mm"
include "adantr.mm"
include "con2d.mm"
include "3impia.mm"
include "bcval3.mm"
include "syld3an3.mm"

theorem bcval4
  let cK: class K
  let cN: class N
  let vk: setvar k
  let vn: setvar n


  assert |- ( ( N e. NN0 /\ K e. ZZ /\ ( K < 0 \/ N < K ) ) -> ( N _C K ) = 0 )

  proof
    cN
    cn0
    wcel
    #
    cK
    cz
    wcel
    #
    cK
    cc0
    clt
    wbr
    #
    cN
    cK
    clt
    wbr
    #
    wo
    #
    cK
    cc0
    cN
    cfz
    co
    wcel
    #
    wn
    #
    cN
    cK
    cbc
    co
    cc0
    wceq
    @0
    @1
    @4
    @6
    @0
    @1
    wa
    @5
    @4
    @0
    @5
    @4
    wn
    #
    wi
    @1
    @0
    @5
    @7
    @0
    @5
    wa
    #
    @2
    wn
    #
    @3
    wn
    #
    @7
    @5
    @9
    @0
    @5
    cc0
    cK
    cle
    wbr
    #
    @9
    cK
    cc0
    cN
    elfzle1
    @5
    cc0
    cr
    wcel
    cK
    cr
    wcel
    #
    @11
    @9
    wb
    0re
    @5
    cK
    cK
    cc0
    cN
    elfzelz
    zred
    #
    cc0
    cK
    lenlt
    sylancr
    mpbid
    adantl
    @8
    cK
    cN
    cle
    wbr
    #
    @10
    @5
    @14
    @0
    cK
    cc0
    cN
    elfzle2
    adantl
    @5
    @12
    cN
    cr
    wcel
    @14
    @10
    wb
    @0
    @13
    cN
    nn0re
    cK
    cN
    lenlt
    syl2anr
    mpbid
    @2
    @3
    ioran
    sylanbrc
    ex
    adantr
    con2d
    3impia
    cK
    cN
    bcval3
    syld3an3
end

include "cr.mm"
include "wcel.mm"
include "ccht.mm"
include "cfv.mm"
include "cc0.mm"
include "wceq.mm"
include "c2.mm"
include "clt.mm"
include "wbr.mm"
include "wn.mm"
include "cle.mm"
include "wne.mm"
include "wb.mm"
include "2re.mm"
include "lenlt.mm"
include "mpan.mm"
include "wa.mm"
include "chtrpcl.mm"
include "rpne0d.mm"
include "ex.mm"
include "sylbird.mm"
include "necon4bd.mm"
include "cchp.mm"
include "chtlepsi.mm"
include "adantr.mm"
include "chpeq0.mm"
include "biimpar.mm"
include "breqtrd.mm"
include "chtge0.mm"
include "chtcl.mm"
include "0re.mm"
include "letri3.mm"
include "sylancl.mm"
include "mpbir2and.mm"
include "impbid.mm"

theorem chteq0
  let cA: class A
  let vk: setvar k
  let vn: setvar n
  let vp: setvar p
  let vx: setvar x
  let cN: class N


  assert |- ( A e. RR -> ( ( theta ` A ) = 0 <-> A < 2 ) )

  proof
    cA
    cr
    wcel
    #
    cA
    ccht
    cfv
    #
    cc0
    wceq
    #
    cA
    c2
    clt
    wbr
    #
    @0
    @3
    @1
    cc0
    @0
    @3
    wn
    #
    c2
    cA
    cle
    wbr
    #
    @1
    cc0
    wne
    #
    c2
    cr
    wcel
    @0
    @5
    @4
    wb
    2re
    c2
    cA
    lenlt
    mpan
    @0
    @5
    @6
    @0
    @5
    wa
    @1
    cA
    chtrpcl
    rpne0d
    ex
    sylbird
    necon4bd
    @0
    @3
    @2
    @0
    @3
    wa
    #
    @2
    @1
    cc0
    cle
    wbr
    #
    cc0
    @1
    cle
    wbr
    #
    @7
    @1
    cA
    cchp
    cfv
    #
    cc0
    cle
    @0
    @1
    @10
    cle
    wbr
    @3
    cA
    chtlepsi
    adantr
    @0
    @10
    cc0
    wceq
    @3
    cA
    chpeq0
    biimpar
    breqtrd
    @0
    @9
    @3
    cA
    chtge0
    adantr
    @7
    @1
    cr
    wcel
    #
    cc0
    cr
    wcel
    @2
    @8
    @9
    wa
    wb
    @0
    @11
    @3
    cA
    chtcl
    adantr
    0re
    @1
    cc0
    letri3
    sylancl
    mpbir2and
    ex
    impbid
end

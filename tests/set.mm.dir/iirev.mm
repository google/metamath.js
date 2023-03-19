include "cr.mm"
include "wcel.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "c1.mm"
include "w3a.mm"
include "cmin.mm"
include "co.mm"
include "cicc.mm"
include "1re.mm"
include "resubcl.mm"
include "mpan.mm"
include "3ad2ant1.mm"
include "simp3.mm"
include "wb.mm"
include "simp1.mm"
include "subge0.mm"
include "sylancr.mm"
include "mpbird.mm"
include "simp2.mm"
include "subge02.mm"
include "mpbid.mm"
include "3jca.mm"
include "0re.mm"
include "elicc2i.mm"
include "3imtr4i.mm"

theorem iirev
  let cX: class X


  assert |- ( X e. ( 0 [,] 1 ) -> ( 1 - X ) e. ( 0 [,] 1 ) )

  proof
    cX
    cr
    wcel
    #
    cc0
    cX
    cle
    wbr
    #
    cX
    c1
    cle
    wbr
    #
    w3a
    #
    c1
    cX
    cmin
    co
    #
    cr
    wcel
    #
    cc0
    @4
    cle
    wbr
    #
    @4
    c1
    cle
    wbr
    #
    w3a
    cX
    cc0
    c1
    cicc
    co
    #
    wcel
    @4
    @8
    wcel
    @3
    @5
    @6
    @7
    @0
    @1
    @5
    @2
    c1
    cr
    wcel
    #
    @0
    @5
    1re
    c1
    cX
    resubcl
    mpan
    3ad2ant1
    @3
    @6
    @2
    @0
    @1
    @2
    simp3
    @3
    @9
    @0
    @6
    @2
    wb
    1re
    @0
    @1
    @2
    simp1
    #
    c1
    cX
    subge0
    sylancr
    mpbird
    @3
    @1
    @7
    @0
    @1
    @2
    simp2
    @3
    @9
    @0
    @1
    @7
    wb
    1re
    @10
    c1
    cX
    subge02
    sylancr
    mpbid
    3jca
    cc0
    c1
    cX
    0re
    1re
    elicc2i
    cc0
    c1
    @4
    0re
    1re
    elicc2i
    3imtr4i
end

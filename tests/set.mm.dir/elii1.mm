include "cc0.mm"
include "c1.mm"
include "c2.mm"
include "cdiv.mm"
include "co.mm"
include "cicc.mm"
include "wcel.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "cr.mm"
include "0re.mm"
include "halfre.mm"
include "elicc2i.mm"
include "simp1bi.mm"
include "a1i.mm"
include "1re.mm"
include "simp3bi.mm"
include "halflt1.mm"
include "ltleii.mm"
include "letrd.mm"
include "pm4.71ri.mm"
include "ancom.mm"
include "an32.mm"
include "w3a.mm"
include "df-3an.mm"
include "bitri.mm"
include "anbi1i.mm"
include "3bitr4i.mm"

theorem elii1
  let cX: class X


  assert |- ( X e. ( 0 [,] ( 1 / 2 ) ) <-> ( X e. ( 0 [,] 1 ) /\ X <_ ( 1 / 2 ) ) )

  proof
    cX
    cc0
    c1
    c2
    cdiv
    co
    #
    cicc
    co
    wcel
    #
    cX
    c1
    cle
    wbr
    #
    @1
    wa
    #
    cX
    cc0
    c1
    cicc
    co
    wcel
    #
    cX
    @0
    cle
    wbr
    #
    wa
    #
    @1
    @2
    @1
    cX
    @0
    c1
    @1
    cX
    cr
    wcel
    #
    cc0
    cX
    cle
    wbr
    #
    @5
    cc0
    @0
    cX
    0re
    halfre
    elicc2i
    #
    simp1bi
    @0
    cr
    wcel
    @1
    halfre
    a1i
    c1
    cr
    wcel
    @1
    1re
    a1i
    @1
    @7
    @8
    @5
    @9
    simp3bi
    @0
    c1
    cle
    wbr
    @1
    @0
    c1
    halfre
    1re
    halflt1
    ltleii
    a1i
    letrd
    pm4.71ri
    @3
    @1
    @2
    wa
    #
    @6
    @2
    @1
    ancom
    @7
    @8
    wa
    #
    @5
    wa
    #
    @2
    wa
    @11
    @2
    wa
    #
    @5
    wa
    @10
    @6
    @11
    @5
    @2
    an32
    @1
    @12
    @2
    @1
    @7
    @8
    @5
    w3a
    @12
    @9
    @7
    @8
    @5
    df-3an
    bitri
    anbi1i
    @4
    @13
    @5
    @4
    @7
    @8
    @2
    w3a
    @13
    cc0
    c1
    cX
    0re
    1re
    elicc2i
    @7
    @8
    @2
    df-3an
    bitri
    anbi1i
    3bitr4i
    bitri
    bitri
end

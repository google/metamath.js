include "cr.mm"
include "wcel.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "c1.mm"
include "c2.mm"
include "cdiv.mm"
include "co.mm"
include "w3a.mm"
include "cmul.mm"
include "cicc.mm"
include "2re.mm"
include "remulcl.mm"
include "mpan.mm"
include "3ad2ant1.mm"
include "wa.mm"
include "0le2.mm"
include "mulge0.mm"
include "mpanl12.mm"
include "3adant3.mm"
include "clt.mm"
include "wb.mm"
include "1re.mm"
include "2pos.mm"
include "pm3.2i.mm"
include "lemuldiv2.mm"
include "mp3an23.mm"
include "biimpar.mm"
include "3adant2.mm"
include "3jca.mm"
include "0re.mm"
include "halfre.mm"
include "elicc2i.mm"
include "3imtr4i.mm"

theorem iihalf1
  let cX: class X


  assert |- ( X e. ( 0 [,] ( 1 / 2 ) ) -> ( 2 x. X ) e. ( 0 [,] 1 ) )

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
    c2
    cdiv
    co
    #
    cle
    wbr
    #
    w3a
    #
    c2
    cX
    cmul
    co
    #
    cr
    wcel
    #
    cc0
    @5
    cle
    wbr
    #
    @5
    c1
    cle
    wbr
    #
    w3a
    cX
    cc0
    @2
    cicc
    co
    wcel
    @5
    cc0
    c1
    cicc
    co
    wcel
    @4
    @6
    @7
    @8
    @0
    @1
    @6
    @3
    c2
    cr
    wcel
    #
    @0
    @6
    2re
    c2
    cX
    remulcl
    mpan
    3ad2ant1
    @0
    @1
    @7
    @3
    @9
    cc0
    c2
    cle
    wbr
    @0
    @1
    wa
    @7
    2re
    0le2
    c2
    cX
    mulge0
    mpanl12
    3adant3
    @0
    @3
    @8
    @1
    @0
    @8
    @3
    @0
    c1
    cr
    wcel
    @9
    cc0
    c2
    clt
    wbr
    #
    wa
    @8
    @3
    wb
    1re
    @9
    @10
    2re
    2pos
    pm3.2i
    cX
    c1
    c2
    lemuldiv2
    mp3an23
    biimpar
    3adant2
    3jca
    cc0
    @2
    cX
    0re
    halfre
    elicc2i
    cc0
    c1
    @5
    0re
    1re
    elicc2i
    3imtr4i
end

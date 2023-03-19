include "cr.mm"
include "wcel.mm"
include "c1.mm"
include "c2.mm"
include "cdiv.mm"
include "co.mm"
include "cle.mm"
include "wbr.mm"
include "w3a.mm"
include "cmul.mm"
include "cmin.mm"
include "cc0.mm"
include "cicc.mm"
include "2re.mm"
include "remulcl.mm"
include "mpan.mm"
include "1re.mm"
include "resubcl.mm"
include "sylancl.mm"
include "3ad2ant1.mm"
include "wb.mm"
include "subge0.mm"
include "clt.mm"
include "wa.mm"
include "2pos.mm"
include "pm3.2i.mm"
include "ledivmul.mm"
include "mp3an13.mm"
include "bitr4d.mm"
include "biimpar.mm"
include "3adant3.mm"
include "caddc.mm"
include "wceq.mm"
include "ax-1cn.mm"
include "2timesi.mm"
include "a1i.mm"
include "breq2d.mm"
include "lemul2.mm"
include "mp3an23.mm"
include "lesubadd.mm"
include "syl.mm"
include "3bitr4d.mm"
include "biimpa.mm"
include "3adant2.mm"
include "3jca.mm"
include "halfre.mm"
include "elicc2i.mm"
include "0re.mm"
include "3imtr4i.mm"

theorem iihalf2
  let cX: class X


  assert |- ( X e. ( ( 1 / 2 ) [,] 1 ) -> ( ( 2 x. X ) - 1 ) e. ( 0 [,] 1 ) )

  proof
    cX
    cr
    wcel
    #
    c1
    c2
    cdiv
    co
    #
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
    c2
    cX
    cmul
    co
    #
    c1
    cmin
    co
    #
    cr
    wcel
    #
    cc0
    @6
    cle
    wbr
    #
    @6
    c1
    cle
    wbr
    #
    w3a
    cX
    @1
    c1
    cicc
    co
    wcel
    @6
    cc0
    c1
    cicc
    co
    wcel
    @4
    @7
    @8
    @9
    @0
    @2
    @7
    @3
    @0
    @5
    cr
    wcel
    #
    c1
    cr
    wcel
    #
    @7
    c2
    cr
    wcel
    #
    @0
    @10
    2re
    c2
    cX
    remulcl
    mpan
    #
    1re
    @5
    c1
    resubcl
    sylancl
    3ad2ant1
    @0
    @2
    @8
    @3
    @0
    @8
    @2
    @0
    @8
    c1
    @5
    cle
    wbr
    #
    @2
    @0
    @10
    @11
    @8
    @14
    wb
    @13
    1re
    @5
    c1
    subge0
    sylancl
    @11
    @0
    @12
    cc0
    c2
    clt
    wbr
    #
    wa
    #
    @2
    @14
    wb
    1re
    @12
    @15
    2re
    2pos
    pm3.2i
    #
    c1
    cX
    c2
    ledivmul
    mp3an13
    bitr4d
    biimpar
    3adant3
    @0
    @3
    @9
    @2
    @0
    @3
    @9
    @0
    @5
    c2
    c1
    cmul
    co
    #
    cle
    wbr
    #
    @5
    c1
    c1
    caddc
    co
    #
    cle
    wbr
    #
    @3
    @9
    @0
    @18
    @20
    @5
    cle
    @18
    @20
    wceq
    @0
    c1
    ax-1cn
    2timesi
    a1i
    breq2d
    @0
    @11
    @16
    @3
    @19
    wb
    1re
    @17
    cX
    c1
    c2
    lemul2
    mp3an23
    @0
    @10
    @9
    @21
    wb
    #
    @13
    @10
    @11
    @11
    @22
    1re
    1re
    @5
    c1
    c1
    lesubadd
    mp3an23
    syl
    3bitr4d
    biimpa
    3adant2
    3jca
    @1
    c1
    cX
    halfre
    1re
    elicc2i
    cc0
    c1
    @6
    0re
    1re
    elicc2i
    3imtr4i
end

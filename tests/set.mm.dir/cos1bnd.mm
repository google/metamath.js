include "c1.mm"
include "c3.mm"
include "cdiv.mm"
include "co.mm"
include "ccos.mm"
include "cfv.mm"
include "clt.mm"
include "wbr.mm"
include "c2.mm"
include "cexp.mm"
include "cmul.mm"
include "cmin.mm"
include "sq1.mm"
include "oveq1i.mm"
include "oveq2i.mm"
include "2cn.mm"
include "3cn.mm"
include "3ne0.mm"
include "divreci.mm"
include "eqtr4i.mm"
include "ax-1cn.mm"
include "divcli.mm"
include "reccli.mm"
include "caddc.mm"
include "df-3.mm"
include "dividi.mm"
include "divdiri.mm"
include "3eqtr3ri.mm"
include "subaddrii.mm"
include "eqtri.mm"
include "cr.mm"
include "wcel.mm"
include "cc0.mm"
include "cle.mm"
include "wa.mm"
include "1re.mm"
include "0lt1.mm"
include "1le1.mm"
include "w3a.mm"
include "cioc.mm"
include "cxr.mm"
include "wb.mm"
include "0xr.mm"
include "elioc2.mm"
include "mp2an.mm"
include "cos01bnd.mm"
include "sylbir.mm"
include "mp3an.mm"
include "simpli.mm"
include "eqbrtrri.mm"
include "simpri.mm"
include "wceq.mm"
include "subadd2i.mm"
include "mpbir.mm"
include "breqtri.mm"
include "pm3.2i.mm"

theorem cos1bnd



  assert |- ( ( 1 / 3 ) < ( cos ` 1 ) /\ ( cos ` 1 ) < ( 2 / 3 ) )

  proof
    c1
    c3
    cdiv
    co
    #
    c1
    ccos
    cfv
    #
    clt
    wbr
    @1
    c2
    c3
    cdiv
    co
    #
    clt
    wbr
    c1
    c2
    c1
    c2
    cexp
    co
    #
    c3
    cdiv
    co
    #
    cmul
    co
    #
    cmin
    co
    #
    @0
    @1
    clt
    @6
    c1
    @2
    cmin
    co
    @0
    @5
    @2
    c1
    cmin
    @5
    c2
    @0
    cmul
    co
    @2
    @4
    @0
    c2
    cmul
    @3
    c1
    c3
    cdiv
    sq1
    oveq1i
    #
    oveq2i
    c2
    c3
    2cn
    3cn
    3ne0
    divreci
    eqtr4i
    oveq2i
    c1
    @2
    @0
    ax-1cn
    c2
    c3
    2cn
    3cn
    3ne0
    divcli
    #
    c3
    3cn
    3ne0
    reccli
    #
    c3
    c3
    cdiv
    co
    c2
    c1
    caddc
    co
    #
    c3
    cdiv
    co
    c1
    @2
    @0
    caddc
    co
    #
    c3
    @10
    c3
    cdiv
    df-3
    oveq1i
    c3
    3cn
    3ne0
    dividi
    c2
    c1
    c3
    2cn
    ax-1cn
    3cn
    3ne0
    divdiri
    3eqtr3ri
    #
    subaddrii
    eqtri
    @6
    @1
    clt
    wbr
    #
    @1
    c1
    @4
    cmin
    co
    #
    clt
    wbr
    #
    c1
    cr
    wcel
    #
    cc0
    c1
    clt
    wbr
    #
    c1
    c1
    cle
    wbr
    #
    @13
    @15
    wa
    #
    1re
    0lt1
    1le1
    @16
    @17
    @18
    w3a
    #
    c1
    cc0
    c1
    cioc
    co
    wcel
    #
    @19
    cc0
    cxr
    wcel
    @16
    @21
    @20
    wb
    0xr
    1re
    cc0
    c1
    c1
    elioc2
    mp2an
    c1
    cos01bnd
    sylbir
    mp3an
    #
    simpli
    eqbrtrri
    @1
    @14
    @2
    clt
    @13
    @15
    @22
    simpri
    @14
    c1
    @0
    cmin
    co
    #
    @2
    @4
    @0
    c1
    cmin
    @7
    oveq2i
    @23
    @2
    wceq
    @11
    c1
    wceq
    @12
    c1
    @0
    @2
    ax-1cn
    @9
    @8
    subadd2i
    mpbir
    eqtri
    breqtri
    pm3.2i
end

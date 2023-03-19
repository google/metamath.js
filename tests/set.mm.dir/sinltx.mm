include "crp.mm"
include "wcel.mm"
include "csin.mm"
include "cfv.mm"
include "clt.mm"
include "wbr.mm"
include "c1.mm"
include "wa.mm"
include "cr.mm"
include "rpre.mm"
include "adantr.mm"
include "resincld.mm"
include "1red.mm"
include "cle.mm"
include "cneg.mm"
include "sinbnd.mm"
include "simprd.mm"
include "syl.mm"
include "simpr.mm"
include "lelttrd.mm"
include "cc0.mm"
include "cioc.mm"
include "co.mm"
include "w3a.mm"
include "df-3an.mm"
include "cxr.mm"
include "wb.mm"
include "0xr.mm"
include "1re.mm"
include "elioc2.mm"
include "mp2an.mm"
include "elrp.mm"
include "anbi1i.mm"
include "3bitr4i.mm"
include "c3.mm"
include "cexp.mm"
include "cdiv.mm"
include "cmin.mm"
include "sin01bnd.mm"
include "sylbir.mm"
include "ltlecasei.mm"

theorem sinltx
  let cA: class A


  assert |- ( A e. RR+ -> ( sin ` A ) < A )

  proof
    cA
    crp
    wcel
    #
    cA
    csin
    cfv
    #
    cA
    clt
    wbr
    #
    c1
    cA
    @0
    c1
    cA
    clt
    wbr
    #
    wa
    #
    @1
    c1
    cA
    @4
    cA
    @0
    cA
    cr
    wcel
    #
    @3
    cA
    rpre
    #
    adantr
    #
    resincld
    @4
    1red
    @7
    @0
    @1
    c1
    cle
    wbr
    #
    @3
    @0
    @5
    @8
    @6
    @5
    c1
    cneg
    @1
    cle
    wbr
    @8
    cA
    sinbnd
    simprd
    syl
    adantr
    @0
    @3
    simpr
    lelttrd
    @0
    cA
    c1
    cle
    wbr
    #
    wa
    #
    cA
    cc0
    c1
    cioc
    co
    wcel
    #
    @2
    @5
    cc0
    cA
    clt
    wbr
    #
    @9
    w3a
    #
    @5
    @12
    wa
    #
    @9
    wa
    @11
    @10
    @5
    @12
    @9
    df-3an
    cc0
    cxr
    wcel
    c1
    cr
    wcel
    @11
    @13
    wb
    0xr
    1re
    cc0
    c1
    cA
    elioc2
    mp2an
    @0
    @14
    @9
    cA
    elrp
    anbi1i
    3bitr4i
    @11
    cA
    cA
    c3
    cexp
    co
    c3
    cdiv
    co
    cmin
    co
    @1
    clt
    wbr
    @2
    cA
    sin01bnd
    simprd
    sylbir
    @0
    1red
    @6
    ltlecasei
end

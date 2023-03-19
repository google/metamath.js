include "crp.mm"
include "cc0.mm"
include "cpnf.mm"
include "cioo.mm"
include "co.mm"
include "cv.mm"
include "cr.mm"
include "wcel.mm"
include "clt.mm"
include "wbr.mm"
include "wa.mm"
include "w3a.mm"
include "ltpnf.mm"
include "adantr.mm"
include "pm4.71i.mm"
include "df-3an.mm"
include "bitr4i.mm"
include "elrp.mm"
include "cxr.mm"
include "wb.mm"
include "0xr.mm"
include "pnfxr.mm"
include "elioo2.mm"
include "mp2an.mm"
include "3bitr4i.mm"
include "eqriv.mm"

theorem dfrp2
  let vx: setvar x


  assert |- RR+ = ( 0 (,) +oo )

  proof
    vx
    crp
    cc0
    cpnf
    cioo
    co
    #
    vx
    cv
    #
    cr
    wcel
    #
    cc0
    @1
    clt
    wbr
    #
    wa
    #
    @2
    @3
    @1
    cpnf
    clt
    wbr
    #
    w3a
    #
    @1
    crp
    wcel
    @1
    @0
    wcel
    #
    @4
    @4
    @5
    wa
    @6
    @4
    @5
    @2
    @5
    @3
    @1
    ltpnf
    adantr
    pm4.71i
    @2
    @3
    @5
    df-3an
    bitr4i
    @1
    elrp
    cc0
    cxr
    wcel
    cpnf
    cxr
    wcel
    @7
    @6
    wb
    0xr
    pnfxr
    cc0
    cpnf
    @1
    elioo2
    mp2an
    3bitr4i
    eqriv
end

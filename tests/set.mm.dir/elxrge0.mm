include "cxr.mm"
include "wcel.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "cpnf.mm"
include "w3a.mm"
include "wa.mm"
include "cicc.mm"
include "co.mm"
include "df-3an.mm"
include "wb.mm"
include "0xr.mm"
include "pnfxr.mm"
include "elicc1.mm"
include "mp2an.mm"
include "pnfge.mm"
include "adantr.mm"
include "pm4.71i.mm"
include "3bitr4i.mm"

theorem elxrge0
  let cA: class A


  assert |- ( A e. ( 0 [,] +oo ) <-> ( A e. RR* /\ 0 <_ A ) )

  proof
    cA
    cxr
    wcel
    #
    cc0
    cA
    cle
    wbr
    #
    cA
    cpnf
    cle
    wbr
    #
    w3a
    #
    @0
    @1
    wa
    #
    @2
    wa
    cA
    cc0
    cpnf
    cicc
    co
    wcel
    #
    @4
    @0
    @1
    @2
    df-3an
    cc0
    cxr
    wcel
    cpnf
    cxr
    wcel
    @5
    @3
    wb
    0xr
    pnfxr
    cc0
    cpnf
    cA
    elicc1
    mp2an
    @4
    @2
    @0
    @2
    @1
    cA
    pnfge
    adantr
    pm4.71i
    3bitr4i
end

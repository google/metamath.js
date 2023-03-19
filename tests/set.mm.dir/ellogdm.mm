include "wcel.mm"
include "cc.mm"
include "cmnf.mm"
include "cc0.mm"
include "cioc.mm"
include "co.mm"
include "cdif.mm"
include "wn.mm"
include "wa.mm"
include "cr.mm"
include "crp.mm"
include "wi.mm"
include "eleq2i.mm"
include "eldif.mm"
include "clt.mm"
include "wbr.mm"
include "cle.mm"
include "w3a.mm"
include "cxr.mm"
include "wb.mm"
include "mnfxr.mm"
include "0re.mm"
include "elioc2.mm"
include "mp2an.mm"
include "df-3an.mm"
include "mnflt.mm"
include "pm4.71i.mm"
include "anbi1i.mm"
include "lenlt.mm"
include "mpan2.mm"
include "elrp.mm"
include "baib.mm"
include "notbid.mm"
include "bitr4d.mm"
include "pm5.32i.mm"
include "bitr3i.mm"
include "3bitri.mm"
include "notbii.mm"
include "iman.mm"
include "bitr4i.mm"
include "anbi2i.mm"

theorem ellogdm
  let cA: class A
  let cD: class D
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume logcn.d: |- D = ( CC \ ( -oo (,] 0 ) )


  assert |- ( A e. D <-> ( A e. CC /\ ( A e. RR -> A e. RR+ ) ) )

  proof
    cA
    cD
    wcel
    cA
    cc
    cmnf
    cc0
    cioc
    co
    #
    cdif
    #
    wcel
    cA
    cc
    wcel
    #
    cA
    @0
    wcel
    #
    wn
    #
    wa
    @2
    cA
    cr
    wcel
    #
    cA
    crp
    wcel
    #
    wi
    #
    wa
    cD
    @1
    cA
    logcn.d
    eleq2i
    cA
    cc
    @0
    eldif
    @4
    @7
    @2
    @4
    @5
    @6
    wn
    #
    wa
    #
    wn
    @7
    @3
    @9
    @3
    @5
    cmnf
    cA
    clt
    wbr
    #
    cA
    cc0
    cle
    wbr
    #
    w3a
    #
    @5
    @10
    wa
    #
    @11
    wa
    #
    @9
    cmnf
    cxr
    wcel
    cc0
    cr
    wcel
    #
    @3
    @12
    wb
    mnfxr
    0re
    cmnf
    cc0
    cA
    elioc2
    mp2an
    @5
    @10
    @11
    df-3an
    @14
    @5
    @11
    wa
    @9
    @5
    @13
    @11
    @5
    @10
    cA
    mnflt
    pm4.71i
    anbi1i
    @5
    @11
    @8
    @5
    @11
    cc0
    cA
    clt
    wbr
    #
    wn
    #
    @8
    @5
    @15
    @11
    @17
    wb
    0re
    cA
    cc0
    lenlt
    mpan2
    @5
    @6
    @16
    @6
    @5
    @16
    cA
    elrp
    baib
    notbid
    bitr4d
    pm5.32i
    bitr3i
    3bitri
    notbii
    @5
    @6
    iman
    bitr4i
    anbi2i
    3bitri
end

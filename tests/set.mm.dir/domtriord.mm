include "con0.mm"
include "wcel.mm"
include "wa.mm"
include "cdom.mm"
include "wbr.mm"
include "csdm.mm"
include "wn.mm"
include "cen.mm"
include "wi.mm"
include "sbth.mm"
include "expcom.mm"
include "a1i.mm"
include "iman.mm"
include "brsdom.mm"
include "xchbinxr.mm"
include "syl6ib.mm"
include "wss.mm"
include "onelss.mm"
include "ssdomg.mm"
include "syld.mm"
include "adantl.mm"
include "con3d.mm"
include "wb.mm"
include "ontri1.mm"
include "ancoms.mm"
include "sylibrd.mm"
include "adantr.mm"
include "ensym.mm"
include "endom.mm"
include "syl.mm"
include "con3i.mm"
include "jcad.mm"
include "syl6ibr.mm"
include "con1d.mm"
include "impbid.mm"

theorem domtriord
  let cA: class A
  let cB: class B


  assert |- ( ( A e. On /\ B e. On ) -> ( A ~<_ B <-> -. B ~< A ) )

  proof
    cA
    con0
    wcel
    #
    cB
    con0
    wcel
    #
    wa
    #
    cA
    cB
    cdom
    wbr
    #
    cB
    cA
    csdm
    wbr
    #
    wn
    #
    @2
    @3
    cB
    cA
    cdom
    wbr
    #
    cB
    cA
    cen
    wbr
    #
    wi
    #
    @5
    @3
    @8
    wi
    @2
    @6
    @3
    @7
    cB
    cA
    sbth
    expcom
    a1i
    @8
    @6
    @7
    wn
    #
    wa
    #
    @4
    @6
    @7
    iman
    cB
    cA
    brsdom
    #
    xchbinxr
    syl6ib
    @2
    @3
    @4
    @2
    @3
    wn
    #
    @10
    @4
    @2
    @12
    @6
    @9
    @2
    @12
    cB
    cA
    wss
    #
    @6
    @2
    @12
    cA
    cB
    wcel
    #
    wn
    #
    @13
    @2
    @14
    @3
    @1
    @14
    @3
    wi
    @0
    @1
    @14
    cA
    cB
    wss
    @3
    cB
    cA
    onelss
    cA
    cB
    con0
    ssdomg
    syld
    adantl
    con3d
    @1
    @0
    @13
    @15
    wb
    cB
    cA
    ontri1
    ancoms
    sylibrd
    @0
    @13
    @6
    wi
    @1
    cB
    cA
    con0
    ssdomg
    adantr
    syld
    @12
    @9
    wi
    @2
    @7
    @3
    @7
    cA
    cB
    cen
    wbr
    @3
    cB
    cA
    ensym
    cA
    cB
    endom
    syl
    con3i
    a1i
    jcad
    @11
    syl6ibr
    con1d
    impbid
end

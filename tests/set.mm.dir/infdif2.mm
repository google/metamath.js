include "ccrd.mm"
include "cdm.mm"
include "wcel.mm"
include "com.mm"
include "cdom.mm"
include "wbr.mm"
include "w3a.mm"
include "cdif.mm"
include "csdm.mm"
include "wn.mm"
include "wi.mm"
include "domnsym.mm"
include "cen.mm"
include "simp3.mm"
include "infdif.mm"
include "ensymd.mm"
include "sdomentr.mm"
include "syl2anc.mm"
include "nsyl3.mm"
include "3expia.mm"
include "3adant2.mm"
include "con2d.mm"
include "wb.mm"
include "domtri2.mm"
include "3adant3.mm"
include "sylibrd.mm"
include "wss.mm"
include "simp1.mm"
include "difss.mm"
include "ssdomg.mm"
include "mpisyl.mm"
include "domtr.mm"
include "ex.mm"
include "syl.mm"
include "impbid.mm"

theorem infdif2
  let cA: class A
  let cB: class B


  assert |- ( ( A e. dom card /\ B e. dom card /\ _om ~<_ A ) -> ( ( A \ B ) ~<_ B <-> A ~<_ B ) )

  proof
    cA
    ccrd
    cdm
    #
    wcel
    #
    cB
    @0
    wcel
    #
    com
    cA
    cdom
    wbr
    #
    w3a
    #
    cA
    cB
    cdif
    #
    cB
    cdom
    wbr
    #
    cA
    cB
    cdom
    wbr
    #
    @4
    @6
    cB
    cA
    csdm
    wbr
    #
    wn
    #
    @7
    @4
    @8
    @6
    @1
    @3
    @8
    @6
    wn
    #
    wi
    @2
    @1
    @3
    @8
    @10
    @6
    cB
    @5
    csdm
    wbr
    #
    @1
    @3
    @8
    w3a
    #
    @5
    cB
    domnsym
    @12
    @8
    cA
    @5
    cen
    wbr
    @11
    @1
    @3
    @8
    simp3
    @12
    @5
    cA
    cA
    cB
    infdif
    ensymd
    cB
    cA
    @5
    sdomentr
    syl2anc
    nsyl3
    3expia
    3adant2
    con2d
    @1
    @2
    @7
    @9
    wb
    @3
    cA
    cB
    domtri2
    3adant3
    sylibrd
    @4
    @5
    cA
    cdom
    wbr
    #
    @7
    @6
    wi
    @4
    @1
    @5
    cA
    wss
    @13
    @1
    @2
    @3
    simp1
    cA
    cB
    difss
    @5
    cA
    @0
    ssdomg
    mpisyl
    @13
    @7
    @6
    @5
    cA
    cB
    domtr
    ex
    syl
    impbid
end

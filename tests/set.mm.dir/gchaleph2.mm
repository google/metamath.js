include "con0.mm"
include "wcel.mm"
include "cale.mm"
include "cfv.mm"
include "cgch.mm"
include "csuc.mm"
include "cpw.mm"
include "ccrd.mm"
include "cdm.mm"
include "cen.mm"
include "wbr.mm"
include "w3a.mm"
include "char.mm"
include "cdom.mm"
include "harcl.mm"
include "csdm.mm"
include "alephon.mm"
include "onenon.mm"
include "harsdom.mm"
include "mp2b.mm"
include "com.mm"
include "wb.mm"
include "wss.mm"
include "simp1.mm"
include "alephgeom.mm"
include "sylib.mm"
include "ssdomg.mm"
include "mpsyl.mm"
include "simp2.mm"
include "wceq.mm"
include "alephsuc.mm"
include "syl.mm"
include "simp3.mm"
include "eqeltrrd.mm"
include "gchpwdom.mm"
include "syl3anc.mm"
include "mpbii.mm"
include "ondomen.mm"
include "sylancr.mm"
include "gchaleph.mm"
include "syld3an3.mm"

theorem gchaleph2
  let cA: class A


  assert |- ( ( A e. On /\ ( aleph ` A ) e. GCH /\ ( aleph ` suc A ) e. GCH ) -> ( aleph ` suc A ) ~~ ~P ( aleph ` A ) )

  proof
    cA
    con0
    wcel
    #
    cA
    cale
    cfv
    #
    cgch
    wcel
    #
    cA
    csuc
    cale
    cfv
    #
    cgch
    wcel
    #
    @1
    cpw
    #
    ccrd
    cdm
    #
    wcel
    #
    @3
    @5
    cen
    wbr
    @0
    @2
    @4
    w3a
    #
    @1
    char
    cfv
    #
    con0
    wcel
    @5
    @9
    cdom
    wbr
    #
    @7
    @1
    harcl
    @8
    @1
    @9
    csdm
    wbr
    #
    @10
    @1
    con0
    wcel
    #
    @1
    @6
    wcel
    @11
    cA
    alephon
    #
    @1
    onenon
    @1
    harsdom
    mp2b
    @8
    com
    @1
    cdom
    wbr
    #
    @2
    @9
    cgch
    wcel
    @11
    @10
    wb
    @12
    @8
    com
    @1
    wss
    #
    @14
    @13
    @8
    @0
    @15
    @0
    @2
    @4
    simp1
    #
    cA
    alephgeom
    sylib
    com
    @1
    con0
    ssdomg
    mpsyl
    @0
    @2
    @4
    simp2
    @8
    @3
    @9
    cgch
    @8
    @0
    @3
    @9
    wceq
    @16
    cA
    alephsuc
    syl
    @0
    @2
    @4
    simp3
    eqeltrrd
    @1
    @9
    gchpwdom
    syl3anc
    mpbii
    @9
    @5
    ondomen
    sylancr
    cA
    gchaleph
    syld3an3
end

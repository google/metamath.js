include "con0.mm"
include "wcel.mm"
include "cale.mm"
include "cfv.mm"
include "cgch.mm"
include "cpw.mm"
include "ccrd.mm"
include "cdm.mm"
include "w3a.mm"
include "csuc.mm"
include "cdom.mm"
include "wbr.mm"
include "cen.mm"
include "csdm.mm"
include "wn.mm"
include "alephsucpw2.mm"
include "wb.mm"
include "alephon.mm"
include "onenon.mm"
include "ax-mp.mm"
include "simp3.mm"
include "domtri2.mm"
include "sylancr.mm"
include "mpbiri.mm"
include "cfn.mm"
include "com.mm"
include "cvv.mm"
include "wss.mm"
include "fvex.mm"
include "simp1.mm"
include "alephgeom.mm"
include "sylib.mm"
include "ssdomg.mm"
include "mpsyl.mm"
include "domnsym.mm"
include "syl.mm"
include "isfinite.mm"
include "sylnibr.mm"
include "wi.mm"
include "simp2.mm"
include "alephordilem1.mm"
include "3ad2ant1.mm"
include "gchi.mm"
include "3expia.mm"
include "syl2anc.mm"
include "mtod.mm"
include "sylancl.mm"
include "mpbird.mm"
include "sbth.mm"

theorem gchaleph
  let cA: class A


  assert |- ( ( A e. On /\ ( aleph ` A ) e. GCH /\ ~P ( aleph ` A ) e. dom card ) -> ( aleph ` suc A ) ~~ ~P ( aleph ` A ) )

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
    @1
    cpw
    #
    ccrd
    cdm
    #
    wcel
    #
    w3a
    #
    cA
    csuc
    #
    cale
    cfv
    #
    @3
    cdom
    wbr
    #
    @3
    @8
    cdom
    wbr
    #
    @8
    @3
    cen
    wbr
    @6
    @9
    @3
    @8
    csdm
    wbr
    wn
    #
    cA
    alephsucpw2
    @6
    @8
    @4
    wcel
    #
    @5
    @9
    @11
    wb
    @8
    con0
    wcel
    @12
    @7
    alephon
    @8
    onenon
    ax-mp
    #
    @0
    @2
    @5
    simp3
    #
    @8
    @3
    domtri2
    sylancr
    mpbiri
    @6
    @10
    @8
    @3
    csdm
    wbr
    #
    wn
    #
    @6
    @15
    @1
    cfn
    wcel
    #
    @6
    @1
    com
    csdm
    wbr
    #
    @17
    @6
    com
    @1
    cdom
    wbr
    #
    @18
    wn
    @1
    cvv
    wcel
    @6
    com
    @1
    wss
    #
    @19
    cA
    cale
    fvex
    @6
    @0
    @20
    @0
    @2
    @5
    simp1
    cA
    alephgeom
    sylib
    com
    @1
    cvv
    ssdomg
    mpsyl
    com
    @1
    domnsym
    syl
    @1
    isfinite
    sylnibr
    @6
    @2
    @1
    @8
    csdm
    wbr
    #
    @15
    @17
    wi
    @0
    @2
    @5
    simp2
    @0
    @2
    @21
    @5
    cA
    alephordilem1
    3ad2ant1
    @2
    @21
    @15
    @17
    @1
    @8
    gchi
    3expia
    syl2anc
    mtod
    @6
    @5
    @12
    @10
    @16
    wb
    @14
    @13
    @3
    @8
    domtri2
    sylancl
    mpbird
    @8
    @3
    sbth
    syl2anc
end

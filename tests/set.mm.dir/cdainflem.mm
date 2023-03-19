include "cun.mm"
include "com.mm"
include "cen.mm"
include "wbr.mm"
include "csdm.mm"
include "wa.mm"
include "wn.mm"
include "wo.mm"
include "unfi2.mm"
include "sdomnen.mm"
include "syl.mm"
include "con2i.mm"
include "ianor.mm"
include "cdom.mm"
include "cvv.mm"
include "wcel.mm"
include "wss.mm"
include "relen.mm"
include "brrelexi.mm"
include "ssun1.mm"
include "ssdomg.mm"
include "mpisyl.mm"
include "domentr.mm"
include "mpancom.mm"
include "anim1i.mm"
include "bren2.mm"
include "sylibr.mm"
include "ex.mm"
include "ssun2.mm"
include "orim12d.mm"
include "syl5bi.mm"
include "mpd.mm"

theorem cdainflem
  let cA: class A
  let cB: class B


  assert |- ( ( A u. B ) ~~ _om -> ( A ~~ _om \/ B ~~ _om ) )

  proof
    cA
    cB
    cun
    #
    com
    cen
    wbr
    #
    cA
    com
    csdm
    wbr
    #
    cB
    com
    csdm
    wbr
    #
    wa
    #
    wn
    #
    cA
    com
    cen
    wbr
    #
    cB
    com
    cen
    wbr
    #
    wo
    #
    @4
    @1
    @4
    @0
    com
    csdm
    wbr
    @1
    wn
    cA
    cB
    unfi2
    @0
    com
    sdomnen
    syl
    con2i
    @5
    @2
    wn
    #
    @3
    wn
    #
    wo
    @1
    @8
    @2
    @3
    ianor
    @1
    @9
    @6
    @10
    @7
    @1
    @9
    @6
    @1
    @9
    wa
    cA
    com
    cdom
    wbr
    #
    @9
    wa
    @6
    @1
    @11
    @9
    cA
    @0
    cdom
    wbr
    #
    @1
    @11
    @1
    @0
    cvv
    wcel
    #
    cA
    @0
    wss
    @12
    @0
    com
    cen
    relen
    brrelexi
    #
    cA
    cB
    ssun1
    cA
    @0
    cvv
    ssdomg
    mpisyl
    cA
    @0
    com
    domentr
    mpancom
    anim1i
    cA
    com
    bren2
    sylibr
    ex
    @1
    @10
    @7
    @1
    @10
    wa
    cB
    com
    cdom
    wbr
    #
    @10
    wa
    @7
    @1
    @15
    @10
    cB
    @0
    cdom
    wbr
    #
    @1
    @15
    @1
    @13
    cB
    @0
    wss
    @16
    @14
    cB
    cA
    ssun2
    cB
    @0
    cvv
    ssdomg
    mpisyl
    cB
    @0
    com
    domentr
    mpancom
    anim1i
    cB
    com
    bren2
    sylibr
    ex
    orim12d
    syl5bi
    mpd
end

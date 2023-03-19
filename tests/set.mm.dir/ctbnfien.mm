include "com.mm"
include "cen.mm"
include "wbr.mm"
include "wa.mm"
include "wss.mm"
include "cfn.mm"
include "wcel.mm"
include "wn.mm"
include "csdm.mm"
include "isfinite.mm"
include "notbii.mm"
include "wo.mm"
include "cdom.mm"
include "cvv.mm"
include "wi.mm"
include "relen.mm"
include "brrelexi.mm"
include "ssdomg.mm"
include "syl.mm"
include "domen2.mm"
include "sylibd.mm"
include "imp.mm"
include "brdom2.mm"
include "sylib.mm"
include "adantlr.mm"
include "ord.mm"
include "syl5bi.mm"
include "impr.mm"
include "wb.mm"
include "enen2.mm"
include "ad2antlr.mm"
include "mpbird.mm"

theorem ctbnfien
  let cA: class A
  let cX: class X
  let cY: class Y


  assert |- ( ( ( X ~~ _om /\ Y ~~ _om ) /\ ( A C_ X /\ -. A e. Fin ) ) -> A ~~ Y )

  proof
    cX
    com
    cen
    wbr
    #
    cY
    com
    cen
    wbr
    #
    wa
    #
    cA
    cX
    wss
    #
    cA
    cfn
    wcel
    #
    wn
    #
    wa
    #
    wa
    cA
    cY
    cen
    wbr
    #
    cA
    com
    cen
    wbr
    #
    @2
    @3
    @5
    @8
    @5
    cA
    com
    csdm
    wbr
    #
    wn
    @2
    @3
    wa
    #
    @8
    @4
    @9
    cA
    isfinite
    notbii
    @10
    @9
    @8
    @0
    @3
    @9
    @8
    wo
    #
    @1
    @0
    @3
    wa
    cA
    com
    cdom
    wbr
    #
    @11
    @0
    @3
    @12
    @0
    @3
    cA
    cX
    cdom
    wbr
    #
    @12
    @0
    cX
    cvv
    wcel
    @3
    @13
    wi
    cX
    com
    cen
    relen
    brrelexi
    cA
    cX
    cvv
    ssdomg
    syl
    cX
    com
    cA
    domen2
    sylibd
    imp
    cA
    com
    brdom2
    sylib
    adantlr
    ord
    syl5bi
    impr
    @1
    @7
    @8
    wb
    @0
    @6
    cY
    com
    cA
    enen2
    ad2antlr
    mpbird
end

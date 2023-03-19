include "wcel.mm"
include "c0.mm"
include "wne.mm"
include "cxp.mm"
include "cdom.mm"
include "wbr.mm"
include "cv.mm"
include "wex.mm"
include "wa.mm"
include "n0.mm"
include "w3a.mm"
include "csn.mm"
include "cen.mm"
include "xpsneng.mm"
include "3adant2.mm"
include "ensymd.mm"
include "cvv.mm"
include "wss.mm"
include "xpexg.mm"
include "3adant3.mm"
include "simp3.mm"
include "snssd.mm"
include "xpss2.mm"
include "syl.mm"
include "ssdomg.mm"
include "sylc.mm"
include "endomtr.mm"
include "syl2anc.mm"
include "3expia.mm"
include "exlimdv.mm"
include "syl5bi.mm"
include "3impia.mm"

theorem xpdom3
  let cA: class A
  let cB: class B
  let cV: class V
  let cW: class W
  let vx: setvar x
  let cC: class C


  assert |- ( ( A e. V /\ B e. W /\ B =/= (/) ) -> A ~<_ ( A X. B ) )

  proof
    cA
    cV
    wcel
    #
    cB
    cW
    wcel
    #
    cB
    c0
    wne
    #
    cA
    cA
    cB
    cxp
    #
    cdom
    wbr
    #
    @2
    vx
    cv
    #
    cB
    wcel
    #
    vx
    wex
    @0
    @1
    wa
    #
    @4
    vx
    cB
    n0
    @7
    @6
    @4
    vx
    @0
    @1
    @6
    @4
    @0
    @1
    @6
    w3a
    #
    cA
    cA
    @5
    csn
    #
    cxp
    #
    cen
    wbr
    @10
    @3
    cdom
    wbr
    #
    @4
    @8
    @10
    cA
    @0
    @6
    @10
    cA
    cen
    wbr
    @1
    cA
    @5
    cV
    cB
    xpsneng
    3adant2
    ensymd
    @8
    @3
    cvv
    wcel
    #
    @10
    @3
    wss
    #
    @11
    @0
    @1
    @12
    @6
    cA
    cB
    cV
    cW
    xpexg
    3adant3
    @8
    @9
    cB
    wss
    @13
    @8
    @5
    cB
    @0
    @1
    @6
    simp3
    snssd
    @9
    cB
    cA
    xpss2
    syl
    @10
    @3
    cvv
    ssdomg
    sylc
    cA
    @10
    @3
    endomtr
    syl2anc
    3expia
    exlimdv
    syl5bi
    3impia
end

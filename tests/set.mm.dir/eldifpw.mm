include "cpw.mm"
include "wcel.mm"
include "wss.mm"
include "wn.mm"
include "wa.mm"
include "cun.mm"
include "cdif.mm"
include "elpwi.mm"
include "unss1.mm"
include "cvv.mm"
include "wb.mm"
include "unexg.mm"
include "mpan2.mm"
include "elpwg.mm"
include "syl.mm"
include "syl5ibr.mm"
include "mpd.mm"
include "unssbd.mm"
include "con3i.mm"
include "anim12i.mm"
include "eldif.mm"
include "sylibr.mm"

theorem eldifpw
  let cA: class A
  let cB: class B
  let cC: class C
  assume eldifpw.1: |- C e. _V


  assert |- ( ( A e. ~P B /\ -. C C_ B ) -> ( A u. C ) e. ( ~P ( B u. C ) \ ~P B ) )

  proof
    cA
    cB
    cpw
    #
    wcel
    #
    cC
    cB
    wss
    #
    wn
    #
    wa
    cA
    cC
    cun
    #
    cB
    cC
    cun
    #
    cpw
    #
    wcel
    #
    @4
    @0
    wcel
    #
    wn
    #
    wa
    @4
    @6
    @0
    cdif
    wcel
    @1
    @7
    @3
    @9
    @1
    cA
    cB
    wss
    #
    @7
    cA
    cB
    elpwi
    @10
    @7
    @1
    @4
    @5
    wss
    #
    cA
    cB
    cC
    unss1
    @1
    @4
    cvv
    wcel
    #
    @7
    @11
    wb
    @1
    cC
    cvv
    wcel
    @12
    eldifpw.1
    cA
    cC
    @0
    cvv
    unexg
    mpan2
    @4
    @5
    cvv
    elpwg
    syl
    syl5ibr
    mpd
    @8
    @2
    @8
    cA
    cC
    cB
    @4
    cB
    elpwi
    unssbd
    con3i
    anim12i
    @4
    @6
    @0
    eldif
    sylibr
end

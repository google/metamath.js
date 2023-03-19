include "cfrgr.mm"
include "wcel.mm"
include "wa.mm"
include "wne.mm"
include "w3a.mm"
include "cv.mm"
include "cs3.mm"
include "c2.mm"
include "cwwlksnon.mm"
include "co.mm"
include "wreu.mm"
include "wrex.mm"
include "c0.mm"
include "frgr2wwlkeu.mm"
include "reurex.mm"
include "ne0i.mm"
include "rexlimivw.mm"
include "3syl.mm"

theorem frgr2wwlkn0
  let cA: class A
  let cB: class B
  let cG: class G
  let cV: class V
  let vc: setvar c
  assume frgr2wwlkeu.v: |- V = ( Vtx ` G )


  assert |- ( ( G e. FriendGraph /\ ( A e. V /\ B e. V ) /\ A =/= B ) -> ( A ( 2 WWalksNOn G ) B ) =/= (/) )

  proof
    cG
    cfrgr
    wcel
    cA
    cV
    wcel
    cB
    cV
    wcel
    wa
    cA
    cB
    wne
    w3a
    cA
    vc
    cv
    cB
    cs3
    #
    cA
    cB
    c2
    cG
    cwwlksnon
    co
    co
    #
    wcel
    #
    vc
    cV
    wreu
    @2
    vc
    cV
    wrex
    @1
    c0
    wne
    #
    cA
    cB
    cG
    cV
    vc
    frgr2wwlkeu.v
    frgr2wwlkeu
    @2
    vc
    cV
    reurex
    @2
    @3
    vc
    cV
    @1
    @0
    ne0i
    rexlimivw
    3syl
end

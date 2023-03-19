include "cfrgr.mm"
include "wcel.mm"
include "wa.mm"
include "wne.mm"
include "w3a.mm"
include "c2.mm"
include "cwwspthsnon.mm"
include "co.mm"
include "chash.mm"
include "cfv.mm"
include "cwwlksnon.mm"
include "c1.mm"
include "wceq.mm"
include "cusgr.mm"
include "frgrusgr.mm"
include "wpthswwlks2on.mm"
include "sylan.mm"
include "3adant2.mm"
include "fveq2d.mm"
include "frgr2wwlk1.mm"
include "eqtrd.mm"

theorem frgr2wsp1
  let cA: class A
  let cB: class B
  let cG: class G
  let cV: class V
  let vc: setvar c
  let vd: setvar d
  let vt: setvar t
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  assume frgr2wwlkeu.v: |- V = ( Vtx ` G )


  assert |- ( ( G e. FriendGraph /\ ( A e. V /\ B e. V ) /\ A =/= B ) -> ( # ` ( A ( 2 WSPathsNOn G ) B ) ) = 1 )

  proof
    cG
    cfrgr
    wcel
    #
    cA
    cV
    wcel
    cB
    cV
    wcel
    wa
    #
    cA
    cB
    wne
    #
    w3a
    #
    cA
    cB
    c2
    cG
    cwwspthsnon
    co
    co
    #
    chash
    cfv
    cA
    cB
    c2
    cG
    cwwlksnon
    co
    co
    #
    chash
    cfv
    c1
    @3
    @4
    @5
    chash
    @0
    @2
    @4
    @5
    wceq
    #
    @1
    @0
    cG
    cusgr
    wcel
    @2
    @6
    cG
    frgrusgr
    cA
    cB
    cG
    wpthswwlks2on
    sylan
    3adant2
    fveq2d
    cA
    cB
    cG
    cV
    frgr2wwlkeu.v
    frgr2wwlk1
    eqtrd
end

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
include "cpr.mm"
include "cedg.mm"
include "cfv.mm"
include "df-3an.mm"
include "eqid.mm"
include "frcond2.mm"
include "syl5bir.mm"
include "3impib.mm"
include "wb.mm"
include "cusgr.mm"
include "cumgr.mm"
include "wi.mm"
include "frgrusgr.mm"
include "usgrumgr.mm"
include "3anan32.mm"
include "umgrwwlks2on.mm"
include "ex.mm"
include "3syl.mm"
include "impl.mm"
include "reubidva.mm"
include "3adant3.mm"
include "mpbird.mm"

theorem frgr2wwlkeu
  let cA: class A
  let cB: class B
  let cG: class G
  let cV: class V
  let vc: setvar c
  assume frgr2wwlkeu.v: |- V = ( Vtx ` G )

  disjoint A c
  disjoint B c
  disjoint G c
  disjoint V c
  assert |- ( ( G e. FriendGraph /\ ( A e. V /\ B e. V ) /\ A =/= B ) -> E! c e. V <" A c B "> e. ( A ( 2 WWalksNOn G ) B ) )

  proof
    cG
    cfrgr
    wcel
    #
    cA
    cV
    wcel
    #
    cB
    cV
    wcel
    #
    wa
    #
    cA
    cB
    wne
    #
    w3a
    cA
    vc
    cv
    #
    cB
    cs3
    cA
    cB
    c2
    cG
    cwwlksnon
    co
    co
    wcel
    #
    vc
    cV
    wreu
    #
    cA
    @5
    cpr
    cG
    cedg
    cfv
    #
    wcel
    @5
    cB
    cpr
    @8
    wcel
    wa
    #
    vc
    cV
    wreu
    #
    @0
    @3
    @4
    @10
    @3
    @4
    wa
    @1
    @2
    @4
    w3a
    @0
    @10
    @1
    @2
    @4
    df-3an
    cA
    cB
    @8
    cG
    cV
    vc
    frgr2wwlkeu.v
    @8
    eqid
    #
    frcond2
    syl5bir
    3impib
    @0
    @3
    @7
    @10
    wb
    @4
    @0
    @3
    wa
    @6
    @9
    vc
    cV
    @0
    @3
    @5
    cV
    wcel
    #
    @6
    @9
    wb
    #
    @0
    cG
    cusgr
    wcel
    cG
    cumgr
    wcel
    #
    @3
    @12
    wa
    #
    @13
    wi
    cG
    frgrusgr
    cG
    usgrumgr
    @15
    @1
    @12
    @2
    w3a
    #
    @14
    @13
    @1
    @12
    @2
    3anan32
    @14
    @16
    @13
    cA
    @5
    cB
    @8
    cG
    cV
    frgr2wwlkeu.v
    @11
    umgrwwlks2on
    ex
    syl5bir
    3syl
    impl
    reubidva
    3adant3
    mpbird
end

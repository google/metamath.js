include "cusgr.mm"
include "wcel.mm"
include "wne.mm"
include "w3a.mm"
include "cpr.mm"
include "wa.mm"
include "cfrgr.mm"
include "wnel.mm"
include "wn.mm"
include "cv.mm"
include "wss.mm"
include "wreu.mm"
include "wi.mm"
include "simprl.mm"
include "simprr.mm"
include "simpl3.mm"
include "4cycl2vnunb.mm"
include "syl3anc.mm"
include "frcond1.mm"
include "pm2.24.mm"
include "syl6com.mm"
include "3ad2ant2.mm"
include "com23.mm"
include "adantr.mm"
include "mpd.mm"
include "pm2.01d.mm"
include "df-nel.mm"
include "sylibr.mm"
include "ex.mm"

theorem 4cyclusnfrgr
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cE: class E
  let cG: class G
  let cV: class V
  let vx: setvar x
  assume 4cyclusnfrgr.v: |- V = ( Vtx ` G )
  assume 4cyclusnfrgr.e: |- E = ( Edg ` G )


  assert |- ( ( G e. USGraph /\ ( A e. V /\ C e. V /\ A =/= C ) /\ ( B e. V /\ D e. V /\ B =/= D ) ) -> ( ( ( { A , B } e. E /\ { B , C } e. E ) /\ ( { C , D } e. E /\ { D , A } e. E ) ) -> G e/ FriendGraph ) )

  proof
    cG
    cusgr
    wcel
    #
    cA
    cV
    wcel
    cC
    cV
    wcel
    cA
    cC
    wne
    w3a
    #
    cB
    cV
    wcel
    cD
    cV
    wcel
    cB
    cD
    wne
    w3a
    #
    w3a
    #
    cA
    cB
    cpr
    cE
    wcel
    cB
    cC
    cpr
    cE
    wcel
    wa
    #
    cC
    cD
    cpr
    cE
    wcel
    cD
    cA
    cpr
    cE
    wcel
    wa
    #
    wa
    #
    cG
    cfrgr
    wnel
    #
    @3
    @6
    wa
    #
    cG
    cfrgr
    wcel
    #
    wn
    #
    @7
    @8
    @9
    @8
    cA
    vx
    cv
    #
    cpr
    @11
    cC
    cpr
    cpr
    cE
    wss
    vx
    cV
    wreu
    #
    wn
    #
    @9
    @10
    wi
    #
    @8
    @4
    @5
    @2
    @13
    @3
    @4
    @5
    simprl
    @3
    @4
    @5
    simprr
    @0
    @1
    @2
    @6
    simpl3
    vx
    cA
    cB
    cC
    cD
    cE
    cV
    4cycl2vnunb
    syl3anc
    @3
    @13
    @14
    wi
    @6
    @3
    @9
    @13
    @10
    @1
    @0
    @9
    @13
    @10
    wi
    #
    wi
    @2
    @9
    @1
    @12
    @15
    cA
    cC
    cE
    cG
    cV
    vx
    4cyclusnfrgr.v
    4cyclusnfrgr.e
    frcond1
    @12
    @10
    pm2.24
    syl6com
    3ad2ant2
    com23
    adantr
    mpd
    pm2.01d
    cG
    cfrgr
    df-nel
    sylibr
    ex
end

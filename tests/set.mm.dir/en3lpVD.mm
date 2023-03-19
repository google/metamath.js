include "ctp.mm"
include "c0.mm"
include "wne.mm"
include "wceq.mm"
include "wo.mm"
include "wcel.mm"
include "w3a.mm"
include "wn.mm"
include "pm2.1.mm"
include "df-ne.mm"
include "bicomi.mm"
include "orbi1i.mm"
include "mpbi.mm"
include "cv.mm"
include "wa.mm"
include "wex.mm"
include "wral.mm"
include "zfregs2.mm"
include "wi.mm"
include "wal.mm"
include "en3lplem2VD.mm"
include "alrimiv.mm"
include "df-ral.mm"
include "sylibr.mm"
include "con3i.mm"
include "syl.mm"
include "idn1.mm"
include "noel.mm"
include "eleq2.mm"
include "notbid.mm"
include "biimprd.mm"
include "e10.mm"
include "tpid3g.mm"
include "e1a.mm"
include "simp3.mm"
include "in1.mm"
include "jaoi.mm"
include "ax-mp.mm"

theorem en3lpVD
  let cA: class A
  let cB: class B
  let cC: class C
  let vx: setvar x
  let vy: setvar y


  assert |- -. ( A e. B /\ B e. C /\ C e. A )

  proof
    cA
    cB
    cC
    ctp
    #
    c0
    wne
    #
    @0
    c0
    wceq
    #
    wo
    #
    cA
    cB
    wcel
    #
    cB
    cC
    wcel
    #
    cC
    cA
    wcel
    #
    w3a
    #
    wn
    #
    @2
    wn
    #
    @2
    wo
    @3
    @2
    pm2.1
    @9
    @1
    @2
    @1
    @9
    @0
    c0
    df-ne
    bicomi
    orbi1i
    mpbi
    @1
    @8
    @2
    @1
    vy
    cv
    #
    @0
    wcel
    @10
    vx
    cv
    #
    wcel
    wa
    vy
    wex
    #
    vx
    @0
    wral
    #
    wn
    @8
    vx
    vy
    @0
    zfregs2
    @7
    @13
    @7
    @11
    @0
    wcel
    @12
    wi
    #
    vx
    wal
    @13
    @7
    @14
    vx
    vx
    vy
    cA
    cB
    cC
    en3lplem2VD
    alrimiv
    @12
    vx
    @0
    df-ral
    sylibr
    con3i
    syl
    @2
    @8
    @2
    @6
    wn
    #
    @8
    @2
    cC
    @0
    wcel
    #
    wn
    #
    @15
    @2
    @2
    cC
    c0
    wcel
    #
    wn
    #
    @17
    @2
    idn1
    cC
    noel
    @2
    @17
    @19
    @2
    @16
    @18
    @0
    c0
    cC
    eleq2
    notbid
    biimprd
    e10
    @6
    @16
    cC
    cA
    cA
    cB
    tpid3g
    con3i
    e1a
    @7
    @6
    @4
    @5
    @6
    simp3
    con3i
    e1a
    in1
    jaoi
    ax-mp
end

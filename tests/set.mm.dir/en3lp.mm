include "wcel.mm"
include "w3a.mm"
include "wn.mm"
include "ctp.mm"
include "c0.mm"
include "wceq.mm"
include "noel.mm"
include "eleq2.mm"
include "mtbiri.mm"
include "tpid3g.mm"
include "nsyl.mm"
include "intn3an3d.mm"
include "wne.mm"
include "cv.mm"
include "cin.mm"
include "wrex.mm"
include "cvv.mm"
include "tpex.mm"
include "zfreg.mm"
include "mpan.mm"
include "en3lplem2.mm"
include "com12.mm"
include "necon2bd.mm"
include "rexlimiv.mm"
include "syl.mm"
include "pm2.61ine.mm"

theorem en3lp
  let cA: class A
  let cB: class B
  let cC: class C
  let vx: setvar x


  assert |- -. ( A e. B /\ B e. C /\ C e. A )

  proof
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
    cA
    cB
    cC
    ctp
    #
    c0
    @5
    c0
    wceq
    #
    @2
    @0
    @1
    @6
    cC
    @5
    wcel
    #
    @2
    @6
    @7
    cC
    c0
    wcel
    cC
    noel
    @5
    c0
    cC
    eleq2
    mtbiri
    cC
    cA
    cA
    cB
    tpid3g
    nsyl
    intn3an3d
    @5
    c0
    wne
    #
    vx
    cv
    #
    @5
    cin
    #
    c0
    wceq
    #
    vx
    @5
    wrex
    #
    @4
    @5
    cvv
    wcel
    @8
    @12
    cA
    cB
    cC
    tpex
    vx
    @5
    cvv
    zfreg
    mpan
    @11
    @4
    vx
    @5
    @9
    @5
    wcel
    #
    @3
    @10
    c0
    @3
    @13
    @10
    c0
    wne
    vx
    cA
    cB
    cC
    en3lplem2
    com12
    necon2bd
    rexlimiv
    syl
    pm2.61ine
end

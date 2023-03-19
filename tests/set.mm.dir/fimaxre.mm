include "cr.mm"
include "wss.mm"
include "cfn.mm"
include "wcel.mm"
include "c0.mm"
include "wne.mm"
include "w3a.mm"
include "cv.mm"
include "clt.mm"
include "wbr.mm"
include "wi.mm"
include "wral.mm"
include "wrex.mm"
include "cle.mm"
include "wor.mm"
include "ltso.mm"
include "soss.mm"
include "mpi.mm"
include "fimaxg.mm"
include "syl3an1.mm"
include "wa.mm"
include "ssel.mm"
include "anim12d.mm"
include "imp.mm"
include "weq.mm"
include "wo.mm"
include "wb.mm"
include "leloe.mm"
include "ancoms.mm"
include "equcom.mm"
include "orbi2i.mm"
include "orcom.mm"
include "neor.mm"
include "3bitri.mm"
include "syl6bb.mm"
include "biimprd.mm"
include "syl.mm"
include "anassrs.mm"
include "ralimdva.mm"
include "reximdva.mm"
include "3ad2ant1.mm"
include "mpd.mm"

theorem fimaxre
  let vx: setvar x
  let vy: setvar y
  let cA: class A

  disjoint A x
  disjoint A y
  disjoint x y
  assert |- ( ( A C_ RR /\ A e. Fin /\ A =/= (/) ) -> E. x e. A A. y e. A y <_ x )

  proof
    cA
    cr
    wss
    #
    cA
    cfn
    wcel
    #
    cA
    c0
    wne
    #
    w3a
    vx
    cv
    #
    vy
    cv
    #
    wne
    @4
    @3
    clt
    wbr
    #
    wi
    #
    vy
    cA
    wral
    #
    vx
    cA
    wrex
    #
    @4
    @3
    cle
    wbr
    #
    vy
    cA
    wral
    #
    vx
    cA
    wrex
    #
    @0
    cA
    clt
    wor
    #
    @1
    @2
    @8
    @0
    cr
    clt
    wor
    @12
    ltso
    cA
    cr
    clt
    soss
    mpi
    vx
    vy
    cA
    clt
    fimaxg
    syl3an1
    @0
    @1
    @8
    @11
    wi
    @2
    @0
    @7
    @10
    vx
    cA
    @0
    @3
    cA
    wcel
    #
    wa
    @6
    @9
    vy
    cA
    @0
    @13
    @4
    cA
    wcel
    #
    @6
    @9
    wi
    #
    @0
    @13
    @14
    wa
    #
    wa
    @3
    cr
    wcel
    #
    @4
    cr
    wcel
    #
    wa
    #
    @15
    @0
    @16
    @19
    @0
    @13
    @17
    @14
    @18
    cA
    cr
    @3
    ssel
    cA
    cr
    @4
    ssel
    anim12d
    imp
    @19
    @9
    @6
    @19
    @9
    @5
    vy
    vx
    weq
    #
    wo
    #
    @6
    @18
    @17
    @9
    @21
    wb
    @4
    @3
    leloe
    ancoms
    @21
    @5
    vx
    vy
    weq
    #
    wo
    @22
    @5
    wo
    @6
    @20
    @22
    @5
    vy
    vx
    equcom
    orbi2i
    @5
    @22
    orcom
    @5
    @3
    @4
    neor
    3bitri
    syl6bb
    biimprd
    syl
    anassrs
    ralimdva
    reximdva
    3ad2ant1
    mpd
end

include "wcel.mm"
include "cpw.mm"
include "wss.mm"
include "c0.mm"
include "wne.mm"
include "w3a.mm"
include "cv.mm"
include "cdif.mm"
include "wrex.mm"
include "crab.mm"
include "wex.mm"
include "wa.mm"
include "n0.mm"
include "difss.mm"
include "wb.mm"
include "elpw2g.mm"
include "ad2antrr.mm"
include "mpbiri.mm"
include "wceq.mm"
include "simpr.mm"
include "sselda.mm"
include "elpwid.mm"
include "dfss4.mm"
include "sylib.mm"
include "eqeltrd.mm"
include "difeq2.mm"
include "eleq1d.mm"
include "rspcev.mm"
include "syl2anc.mm"
include "ex.mm"
include "exlimdv.mm"
include "syl5bi.mm"
include "3impia.mm"
include "rabn0.mm"
include "sylibr.mm"

theorem fin23lem7
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cV: class V
  let vc: setvar c
  let vv: setvar v
  let vw: setvar w
  let vy: setvar y
  let vz: setvar z
  let wch: wff ch
  let wph: wff ph
  let wps: wff ps
  let wth: wff th

  disjoint A x
  disjoint B x
  disjoint c v
  disjoint c w
  disjoint c x
  disjoint c y
  disjoint c z
  disjoint A c
  disjoint v w
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint A v
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint A w
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint B c
  disjoint B v
  disjoint B w
  disjoint B y
  disjoint B z
  disjoint ch z
  disjoint ph v
  disjoint V y
  disjoint ps x
  disjoint th w
  assert |- ( ( A e. V /\ B C_ ~P A /\ B =/= (/) ) -> { x e. ~P A | ( A \ x ) e. B } =/= (/) )

  proof
    cA
    cV
    wcel
    #
    cB
    cA
    cpw
    #
    wss
    #
    cB
    c0
    wne
    #
    w3a
    cA
    vx
    cv
    #
    cdif
    #
    cB
    wcel
    #
    vx
    @1
    wrex
    #
    @6
    vx
    @1
    crab
    c0
    wne
    @0
    @2
    @3
    @7
    @3
    vy
    cv
    #
    cB
    wcel
    #
    vy
    wex
    @0
    @2
    wa
    #
    @7
    vy
    cB
    n0
    @10
    @9
    @7
    vy
    @10
    @9
    @7
    @10
    @9
    wa
    #
    cA
    @8
    cdif
    #
    @1
    wcel
    #
    cA
    @12
    cdif
    #
    cB
    wcel
    #
    @7
    @11
    @13
    @12
    cA
    wss
    #
    cA
    @8
    difss
    @0
    @13
    @16
    wb
    @2
    @9
    @12
    cA
    cV
    elpw2g
    ad2antrr
    mpbiri
    @11
    @14
    @8
    cB
    @11
    @8
    cA
    wss
    @14
    @8
    wceq
    @11
    @8
    cA
    @10
    cB
    @1
    @8
    @0
    @2
    simpr
    sselda
    elpwid
    @8
    cA
    dfss4
    sylib
    @10
    @9
    simpr
    eqeltrd
    @6
    @15
    vx
    @12
    @1
    @4
    @12
    wceq
    @5
    @14
    cB
    @4
    @12
    cA
    difeq2
    eleq1d
    rspcev
    syl2anc
    ex
    exlimdv
    syl5bi
    3impia
    @6
    vx
    @1
    rabn0
    sylibr
end

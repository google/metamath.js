include "w-bnj15.mm"
include "wss.mm"
include "c0.mm"
include "wne.mm"
include "w3a.mm"
include "cv.mm"
include "wbr.mm"
include "wn.mm"
include "wral.mm"
include "wrex.mm"
include "bnj69.mm"
include "wcel.mm"
include "wa.mm"
include "wex.mm"
include "nfv.mm"
include "nfcii.mm"
include "nfcri.mm"
include "nfral.mm"
include "nfan.mm"
include "weq.mm"
include "eleq1.mm"
include "breq2.mm"
include "notbid.mm"
include "ralbidv.mm"
include "anbi12d.mm"
include "cbvex.mm"
include "df-rex.mm"
include "3bitr4i.mm"
include "sylibr.mm"

theorem bnj1228
  let vx: setvar x
  let vy: setvar y
  let vw: setvar w
  let cA: class A
  let cB: class B
  let cR: class R
  let vz: setvar z
  assume bnj1228.1: |- ( w e. B -> A. x w e. B )

  disjoint A y
  disjoint B w
  disjoint B y
  disjoint w y
  disjoint R x
  disjoint R y
  disjoint x y
  disjoint w x
  disjoint A z
  disjoint y z
  disjoint B z
  disjoint w z
  disjoint R z
  disjoint x z
  assert |- ( ( R _FrSe A /\ B C_ A /\ B =/= (/) ) -> E. x e. B A. y e. B -. y R x )

  proof
    cA
    cR
    w-bnj15
    cB
    cA
    wss
    cB
    c0
    wne
    w3a
    vy
    cv
    #
    vz
    cv
    #
    cR
    wbr
    #
    wn
    #
    vy
    cB
    wral
    #
    vz
    cB
    wrex
    #
    @0
    vx
    cv
    #
    cR
    wbr
    #
    wn
    #
    vy
    cB
    wral
    #
    vx
    cB
    wrex
    #
    vz
    vy
    cA
    cB
    cR
    bnj69
    @6
    cB
    wcel
    #
    @9
    wa
    #
    vx
    wex
    @1
    cB
    wcel
    #
    @4
    wa
    #
    vz
    wex
    @10
    @5
    @12
    @14
    vx
    vz
    @12
    vz
    nfv
    @13
    @4
    vx
    vx
    vz
    cB
    vx
    vw
    cB
    bnj1228.1
    nfcii
    #
    nfcri
    @3
    vx
    vy
    cB
    @15
    @3
    vx
    nfv
    nfral
    nfan
    vx
    vz
    weq
    #
    @11
    @13
    @9
    @4
    @6
    @1
    cB
    eleq1
    @16
    @8
    @3
    vy
    cB
    @16
    @7
    @2
    @6
    @1
    @0
    cR
    breq2
    notbid
    ralbidv
    anbi12d
    cbvex
    @9
    vx
    cB
    df-rex
    @4
    vz
    cB
    df-rex
    3bitr4i
    sylibr
end

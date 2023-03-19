include "wcel.mm"
include "cfbas.mm"
include "cfv.mm"
include "cpw.mm"
include "wss.mm"
include "c0.mm"
include "wne.mm"
include "wnel.mm"
include "cv.mm"
include "cin.mm"
include "wral.mm"
include "w3a.mm"
include "wa.mm"
include "wrex.mm"
include "isfbas.mm"
include "wex.mm"
include "elin.mm"
include "selpw.mm"
include "anbi2i.mm"
include "bitri.mm"
include "exbii.mm"
include "n0.mm"
include "df-rex.mm"
include "3bitr4i.mm"
include "2ralbii.mm"
include "3anbi3i.mm"
include "syl6bb.mm"

theorem isfbas2
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cF: class F

  disjoint x y
  disjoint x z
  disjoint F x
  disjoint y z
  disjoint F y
  disjoint F z
  disjoint B x
  disjoint B y
  disjoint B z
  assert |- ( B e. A -> ( F e. ( fBas ` B ) <-> ( F C_ ~P B /\ ( F =/= (/) /\ (/) e/ F /\ A. x e. F A. y e. F E. z e. F z C_ ( x i^i y ) ) ) ) )

  proof
    cB
    cA
    wcel
    cF
    cB
    cfbas
    cfv
    wcel
    cF
    cB
    cpw
    wss
    #
    cF
    c0
    wne
    #
    c0
    cF
    wnel
    #
    cF
    vx
    cv
    vy
    cv
    cin
    #
    cpw
    #
    cin
    #
    c0
    wne
    #
    vy
    cF
    wral
    vx
    cF
    wral
    #
    w3a
    #
    wa
    @0
    @1
    @2
    vz
    cv
    #
    @3
    wss
    #
    vz
    cF
    wrex
    #
    vy
    cF
    wral
    vx
    cF
    wral
    #
    w3a
    #
    wa
    vx
    vy
    cA
    cB
    cF
    isfbas
    @8
    @13
    @0
    @7
    @12
    @1
    @2
    @6
    @11
    vx
    vy
    cF
    cF
    @9
    @5
    wcel
    #
    vz
    wex
    @9
    cF
    wcel
    #
    @10
    wa
    #
    vz
    wex
    @6
    @11
    @14
    @16
    vz
    @14
    @15
    @9
    @4
    wcel
    #
    wa
    @16
    @9
    cF
    @4
    elin
    @17
    @10
    @15
    vz
    @3
    selpw
    anbi2i
    bitri
    exbii
    vz
    @5
    n0
    @10
    vz
    cF
    df-rex
    3bitr4i
    2ralbii
    3anbi3i
    anbi2i
    syl6bb
end

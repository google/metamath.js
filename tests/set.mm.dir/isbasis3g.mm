include "wcel.mm"
include "ctb.mm"
include "wel.mm"
include "cv.mm"
include "cin.mm"
include "wss.mm"
include "wa.mm"
include "wrex.mm"
include "wral.mm"
include "cuni.mm"
include "w3a.mm"
include "isbasis2g.mm"
include "elssuni.mm"
include "rgen.mm"
include "eluni2.mm"
include "biimpi.mm"
include "pm3.2i.mm"
include "biantrur.mm"
include "df-3an.mm"
include "bitr4i.mm"
include "syl6bb.mm"

theorem isbasis3g
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let cB: class B
  let cC: class C

  disjoint w x
  disjoint w y
  disjoint w z
  disjoint B w
  disjoint x y
  disjoint x z
  disjoint B x
  disjoint y z
  disjoint B y
  disjoint B z
  assert |- ( B e. C -> ( B e. TopBases <-> ( A. x e. B x C_ U. B /\ A. x e. U. B E. y e. B x e. y /\ A. x e. B A. y e. B A. z e. ( x i^i y ) E. w e. B ( z e. w /\ w C_ ( x i^i y ) ) ) ) )

  proof
    cB
    cC
    wcel
    cB
    ctb
    wcel
    vz
    vw
    wel
    vw
    cv
    vx
    cv
    #
    vy
    cv
    cin
    #
    wss
    wa
    vw
    cB
    wrex
    vz
    @1
    wral
    vy
    cB
    wral
    vx
    cB
    wral
    #
    @0
    cB
    cuni
    #
    wss
    #
    vx
    cB
    wral
    #
    vx
    vy
    wel
    vy
    cB
    wrex
    #
    vx
    @3
    wral
    #
    @2
    w3a
    #
    vx
    vy
    vz
    vw
    cB
    cC
    isbasis2g
    @2
    @5
    @7
    wa
    #
    @2
    wa
    @8
    @9
    @2
    @5
    @7
    @4
    vx
    cB
    @0
    cB
    elssuni
    rgen
    @6
    vx
    @3
    @0
    @3
    wcel
    @6
    vy
    @0
    cB
    eluni2
    biimpi
    rgen
    pm3.2i
    biantrur
    @5
    @7
    @2
    df-3an
    bitr4i
    syl6bb
end

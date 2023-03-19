include "wor.mm"
include "csup.mm"
include "cv.mm"
include "wbr.mm"
include "wn.mm"
include "wral.mm"
include "wrex.mm"
include "wi.mm"
include "wa.mm"
include "crio.mm"
include "wceq.mm"
include "crab.mm"
include "cuni.mm"
include "wreu.mm"
include "simpl.mm"
include "simpr.mm"
include "supeu.mm"
include "riotauni.mm"
include "syl.mm"
include "df-sup.mm"
include "syl6reqr.mm"
include "c0.mm"
include "rabn0.mm"
include "necon1bbii.mm"
include "biimpi.mm"
include "unieqd.mm"
include "uni0.mm"
include "syl6eq.mm"
include "syl5eq.mm"
include "reurex.mm"
include "con3i.mm"
include "riotaund.mm"
include "eqtr4d.mm"
include "adantl.mm"
include "pm2.61dan.mm"

theorem supval2
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cR: class R
  let vw: setvar w
  let cC: class C
  assume supmo.1: |- ( ph -> R Or A )

  disjoint x y
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint R x
  disjoint R y
  disjoint R z
  disjoint B x
  disjoint B y
  disjoint B z
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint A w
  disjoint R w
  disjoint B w
  disjoint C w
  disjoint ph w
  assert |- ( ph -> sup ( B , A , R ) = ( iota_ x e. A ( A. y e. B -. x R y /\ A. y e. A ( y R x -> E. z e. B y R z ) ) ) )

  proof
    wph
    cA
    cR
    wor
    #
    cB
    cA
    cR
    csup
    #
    vx
    cv
    #
    vy
    cv
    #
    cR
    wbr
    wn
    vy
    cB
    wral
    @3
    @2
    cR
    wbr
    @3
    vz
    cv
    cR
    wbr
    vz
    cB
    wrex
    wi
    vy
    cA
    wral
    wa
    #
    vx
    cA
    crio
    #
    wceq
    #
    supmo.1
    @0
    @4
    vx
    cA
    wrex
    #
    @6
    @0
    @7
    wa
    #
    @5
    @4
    vx
    cA
    crab
    #
    cuni
    #
    @1
    @8
    @4
    vx
    cA
    wreu
    #
    @5
    @10
    wceq
    @8
    vx
    vy
    vz
    cA
    cB
    cR
    @0
    @7
    simpl
    @0
    @7
    simpr
    supeu
    @4
    vx
    cA
    riotauni
    syl
    vx
    vy
    vz
    cB
    cA
    cR
    df-sup
    #
    syl6reqr
    @7
    wn
    #
    @6
    @0
    @13
    @1
    c0
    @5
    @13
    @1
    @10
    c0
    @12
    @13
    @10
    c0
    cuni
    c0
    @13
    @9
    c0
    @13
    @9
    c0
    wceq
    @7
    @9
    c0
    @4
    vx
    cA
    rabn0
    necon1bbii
    biimpi
    unieqd
    uni0
    syl6eq
    syl5eq
    @13
    @11
    wn
    @5
    c0
    wceq
    @11
    @7
    @4
    vx
    cA
    reurex
    con3i
    @4
    vx
    cA
    riotaund
    syl
    eqtr4d
    adantl
    pm2.61dan
    syl
end

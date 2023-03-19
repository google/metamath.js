include "copab.mm"
include "cv.mm"
include "cop.mm"
include "wceq.mm"
include "wa.mm"
include "wex.mm"
include "cab.mm"
include "cxp.mm"
include "df-opab.mm"
include "wcel.mm"
include "simprl.mm"
include "opelxpd.mm"
include "adantrl.mm"
include "eqeltrd.mm"
include "ex.mm"
include "exlimdvv.mm"
include "abssdv.mm"
include "syl5eqss.mm"

theorem opabssxpd
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let vz: setvar z
  assume opabssxpd.x: |- ( ( ph /\ ps ) -> x e. A )
  assume opabssxpd.y: |- ( ( ph /\ ps ) -> y e. B )

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B x
  disjoint B y
  disjoint ph x
  disjoint ph y
  disjoint x z
  disjoint y z
  disjoint A z
  disjoint B z
  disjoint ph z
  disjoint ps z
  assert |- ( ph -> { <. x , y >. | ps } C_ ( A X. B ) )

  proof
    wph
    wps
    vx
    vy
    copab
    vz
    cv
    #
    vx
    cv
    #
    vy
    cv
    #
    cop
    #
    wceq
    #
    wps
    wa
    #
    vy
    wex
    vx
    wex
    #
    vz
    cab
    cA
    cB
    cxp
    #
    wps
    vx
    vy
    vz
    df-opab
    wph
    @6
    vz
    @7
    wph
    @5
    @0
    @7
    wcel
    #
    vx
    vy
    wph
    @5
    @8
    wph
    @5
    wa
    @0
    @3
    @7
    wph
    @4
    wps
    simprl
    wph
    wps
    @3
    @7
    wcel
    @4
    wph
    wps
    wa
    @1
    @2
    cA
    cB
    opabssxpd.x
    opabssxpd.y
    opelxpd
    adantrl
    eqeltrd
    ex
    exlimdvv
    abssdv
    syl5eqss
end

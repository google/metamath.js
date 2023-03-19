include "copab.mm"
include "cv.mm"
include "cop.mm"
include "wceq.mm"
include "wa.mm"
include "wex.mm"
include "cab.mm"
include "df-opab.mm"
include "wcel.mm"
include "eleq1.mm"
include "biimprd.mm"
include "impel.mm"
include "exlimivv.mm"
include "abssi.mm"
include "eqsstri.mm"

theorem opabssi
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let vz: setvar z
  assume opabssi.1: |- ( ph -> <. x , y >. e. A )

  disjoint A x
  disjoint A y
  disjoint x y
  disjoint A z
  disjoint x z
  disjoint y z
  disjoint ph z
  assert |- { <. x , y >. | ph } C_ A

  proof
    wph
    vx
    vy
    copab
    vz
    cv
    #
    vx
    cv
    vy
    cv
    cop
    #
    wceq
    #
    wph
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
    wph
    vx
    vy
    vz
    df-opab
    @4
    vz
    cA
    @3
    @0
    cA
    wcel
    #
    vx
    vy
    @2
    @1
    cA
    wcel
    #
    @5
    wph
    @2
    @5
    @6
    @0
    @1
    cA
    eleq1
    biimprd
    opabssi.1
    impel
    exlimivv
    abssi
    eqsstri
end

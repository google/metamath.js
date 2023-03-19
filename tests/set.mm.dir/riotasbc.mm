include "wreu.mm"
include "crio.mm"
include "cab.mm"
include "wcel.mm"
include "wsbc.mm"
include "crab.mm"
include "rabssab.mm"
include "riotacl2.mm"
include "sseldi.mm"
include "df-sbc.mm"
include "sylibr.mm"

theorem riotasbc
  let wph: wff ph
  let vx: setvar x
  let cA: class A


  assert |- ( E! x e. A ph -> [. ( iota_ x e. A ph ) / x ]. ph )

  proof
    wph
    vx
    cA
    wreu
    #
    wph
    vx
    cA
    crio
    #
    wph
    vx
    cab
    #
    wcel
    wph
    vx
    @1
    wsbc
    @0
    wph
    vx
    cA
    crab
    @2
    @1
    wph
    vx
    cA
    rabssab
    wph
    vx
    cA
    riotacl2
    sseldi
    wph
    vx
    @1
    df-sbc
    sylibr
end

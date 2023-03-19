include "wa.mm"
include "wb.mm"
include "iba.mm"
include "bicomd.mm"
include "adantl.mm"
include "pm5.21ni.mm"
include "orri.mm"

theorem pm5.54
  let wph: wff ph
  let wps: wff ps


  assert |- ( ( ( ph /\ ps ) <-> ph ) \/ ( ( ph /\ ps ) <-> ps ) )

  proof
    wph
    wps
    wa
    #
    wph
    wb
    #
    @0
    wps
    wb
    @0
    @1
    wps
    wps
    @1
    wph
    wps
    wph
    @0
    wps
    wph
    iba
    bicomd
    #
    adantl
    @2
    pm5.21ni
    orri
end

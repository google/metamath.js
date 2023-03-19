include "wa.mm"
include "anidm.mm"
include "anbi1i.mm"
include "an4.mm"
include "bitr3i.mm"

theorem anandi
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch


  assert |- ( ( ph /\ ( ps /\ ch ) ) <-> ( ( ph /\ ps ) /\ ( ph /\ ch ) ) )

  proof
    wph
    wps
    wch
    wa
    #
    wa
    wph
    wph
    wa
    #
    @0
    wa
    wph
    wps
    wa
    wph
    wch
    wa
    wa
    @1
    wph
    @0
    wph
    anidm
    anbi1i
    wph
    wph
    wps
    wch
    an4
    bitr3i
end

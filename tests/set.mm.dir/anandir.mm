include "wa.mm"
include "anidm.mm"
include "anbi2i.mm"
include "an4.mm"
include "bitr3i.mm"

theorem anandir
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch


  assert |- ( ( ( ph /\ ps ) /\ ch ) <-> ( ( ph /\ ch ) /\ ( ps /\ ch ) ) )

  proof
    wph
    wps
    wa
    #
    wch
    wa
    @0
    wch
    wch
    wa
    #
    wa
    wph
    wch
    wa
    wps
    wch
    wa
    wa
    @1
    wch
    @0
    wch
    anidm
    anbi2i
    wph
    wps
    wch
    wch
    an4
    bitr3i
end

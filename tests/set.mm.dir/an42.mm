include "wa.mm"
include "an4.mm"
include "ancom.mm"
include "anbi2i.mm"
include "bitri.mm"

theorem an42
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th


  assert |- ( ( ( ph /\ ps ) /\ ( ch /\ th ) ) <-> ( ( ph /\ ch ) /\ ( th /\ ps ) ) )

  proof
    wph
    wps
    wa
    wch
    wth
    wa
    wa
    wph
    wch
    wa
    #
    wps
    wth
    wa
    #
    wa
    @0
    wth
    wps
    wa
    #
    wa
    wph
    wps
    wch
    wth
    an4
    @1
    @2
    @0
    wps
    wth
    ancom
    anbi2i
    bitri
end

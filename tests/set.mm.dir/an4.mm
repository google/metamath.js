include "wa.mm"
include "an12.mm"
include "anbi2i.mm"
include "anass.mm"
include "3bitr4i.mm"

theorem an4
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th


  assert |- ( ( ( ph /\ ps ) /\ ( ch /\ th ) ) <-> ( ( ph /\ ch ) /\ ( ps /\ th ) ) )

  proof
    wph
    wps
    wch
    wth
    wa
    #
    wa
    #
    wa
    wph
    wch
    wps
    wth
    wa
    #
    wa
    #
    wa
    wph
    wps
    wa
    @0
    wa
    wph
    wch
    wa
    @2
    wa
    @1
    @3
    wph
    wps
    wch
    wth
    an12
    anbi2i
    wph
    wps
    @0
    anass
    wph
    wch
    @2
    anass
    3bitr4i
end

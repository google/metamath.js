include "wa.mm"
include "wo.mm"
include "ordir.mm"
include "ordi.mm"
include "anbi12i.mm"
include "bitri.mm"

theorem orddi
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th


  assert |- ( ( ( ph /\ ps ) \/ ( ch /\ th ) ) <-> ( ( ( ph \/ ch ) /\ ( ph \/ th ) ) /\ ( ( ps \/ ch ) /\ ( ps \/ th ) ) ) )

  proof
    wph
    wps
    wa
    wch
    wth
    wa
    #
    wo
    wph
    @0
    wo
    #
    wps
    @0
    wo
    #
    wa
    wph
    wch
    wo
    wph
    wth
    wo
    wa
    #
    wps
    wch
    wo
    wps
    wth
    wo
    wa
    #
    wa
    wph
    wps
    @0
    ordir
    @1
    @3
    @2
    @4
    wph
    wch
    wth
    ordi
    wps
    wch
    wth
    ordi
    anbi12i
    bitri
end

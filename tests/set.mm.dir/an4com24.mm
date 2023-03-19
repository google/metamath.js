include "wa.mm"
include "an43.mm"
include "ancom.mm"
include "anbi2i.mm"
include "bitri.mm"

theorem an4com24
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let vk: setvar k
  let vx: setvar x


  assert |- ( ( ( ph /\ ps ) /\ ( ch /\ th ) ) <-> ( ( ph /\ th ) /\ ( ch /\ ps ) ) )

  proof
    wph
    wps
    wa
    wch
    wth
    wa
    wa
    wph
    wth
    wa
    #
    wps
    wch
    wa
    #
    wa
    @0
    wch
    wps
    wa
    #
    wa
    wph
    wps
    wch
    wth
    an43
    @1
    @2
    @0
    wps
    wch
    ancom
    anbi2i
    bitri
end

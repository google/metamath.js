include "wa.mm"
include "w3a.mm"
include "3anass.mm"
include "ancom.mm"
include "anbi1i.mm"
include "anass.mm"
include "bicomi.mm"
include "anbi2i.mm"
include "bitri.mm"

theorem 4an21
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let vk: setvar k
  let vx: setvar x


  assert |- ( ( ( ph /\ ps ) /\ ch /\ th ) <-> ( ps /\ ( ph /\ ch /\ th ) ) )

  proof
    wph
    wps
    wa
    #
    wch
    wth
    w3a
    @0
    wch
    wth
    wa
    #
    wa
    #
    wps
    wph
    wch
    wth
    w3a
    #
    wa
    #
    @0
    wch
    wth
    3anass
    @2
    wps
    wph
    wa
    #
    @1
    wa
    #
    @4
    @0
    @5
    @1
    wph
    wps
    ancom
    anbi1i
    @6
    wps
    wph
    @1
    wa
    #
    wa
    @4
    wps
    wph
    @1
    anass
    @7
    @3
    wps
    @3
    @7
    wph
    wch
    wth
    3anass
    bicomi
    anbi2i
    bitri
    bitri
    bitri
end

include "wa.mm"
include "ancom.mm"
include "sylbi.mm"
include "3impdi.mm"

theorem uun2131p1
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume uun2131p1.1: |- ( ( ( ph /\ ch ) /\ ( ph /\ ps ) ) -> th )


  assert |- ( ( ph /\ ps /\ ch ) -> th )

  proof
    wph
    wps
    wch
    wth
    wph
    wps
    wa
    #
    wph
    wch
    wa
    #
    wa
    @1
    @0
    wa
    wth
    @0
    @1
    ancom
    uun2131p1.1
    sylbi
    3impdi
end

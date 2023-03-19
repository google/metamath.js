include "w3a.mm"
include "wa.mm"
include "3anass.mm"
include "ancom.mm"
include "bitri.mm"
include "sylbi.mm"

theorem uun132p1
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume uun132p1.1: |- ( ( ( ps /\ ch ) /\ ph ) -> th )


  assert |- ( ( ph /\ ps /\ ch ) -> th )

  proof
    wph
    wps
    wch
    w3a
    #
    wps
    wch
    wa
    #
    wph
    wa
    #
    wth
    @0
    wph
    @1
    wa
    @2
    wph
    wps
    wch
    3anass
    wph
    @1
    ancom
    bitri
    uun132p1.1
    sylbi
end

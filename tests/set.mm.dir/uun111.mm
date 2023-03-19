include "w3a.mm"
include "wa.mm"
include "3anass.mm"
include "anabs5.mm"
include "anidm.mm"
include "3bitri.mm"
include "sylbir.mm"

theorem uun111
  let wph: wff ph
  let wps: wff ps
  assume uun111.1: |- ( ( ph /\ ph /\ ph ) -> ps )


  assert |- ( ph -> ps )

  proof
    wph
    wph
    wph
    wph
    w3a
    #
    wps
    @0
    wph
    wph
    wph
    wa
    #
    wa
    @1
    wph
    wph
    wph
    wph
    3anass
    wph
    wph
    anabs5
    wph
    anidm
    3bitri
    uun111.1
    sylbir
end

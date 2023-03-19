include "wtru.mm"
include "w3a.mm"
include "wa.mm"
include "3anass.mm"
include "truan.mm"
include "anidm.mm"
include "3bitri.mm"
include "sylbir.mm"

theorem uunT11
  let wph: wff ph
  let wps: wff ps
  assume uunT11.1: |- ( ( T. /\ ph /\ ph ) -> ps )


  assert |- ( ph -> ps )

  proof
    wph
    wtru
    wph
    wph
    w3a
    #
    wps
    @0
    wtru
    wph
    wph
    wa
    #
    wa
    @1
    wph
    wtru
    wph
    wph
    3anass
    @1
    truan
    wph
    anidm
    3bitri
    uunT11.1
    sylbir
end

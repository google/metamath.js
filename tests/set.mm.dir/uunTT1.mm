include "wtru.mm"
include "w3a.mm"
include "wa.mm"
include "3anass.mm"
include "anabs5.mm"
include "truan.mm"
include "3bitri.mm"
include "sylbir.mm"

theorem uunTT1
  let wph: wff ph
  let wps: wff ps
  assume uunTT1.1: |- ( ( T. /\ T. /\ ph ) -> ps )


  assert |- ( ph -> ps )

  proof
    wph
    wtru
    wtru
    wph
    w3a
    #
    wps
    @0
    wtru
    wtru
    wph
    wa
    #
    wa
    @1
    wph
    wtru
    wtru
    wph
    3anass
    wtru
    wph
    anabs5
    wph
    truan
    3bitri
    uunTT1.1
    sylbir
end

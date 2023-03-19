include "wtru.mm"
include "wa.mm"
include "ancom.mm"
include "truan.mm"
include "bitri.mm"
include "sylbir.mm"

theorem uunT1p1
  let wph: wff ph
  let wps: wff ps
  assume uunT1p1.1: |- ( ( ph /\ T. ) -> ps )


  assert |- ( ph -> ps )

  proof
    wph
    wph
    wtru
    wa
    #
    wps
    @0
    wtru
    wph
    wa
    wph
    wph
    wtru
    ancom
    wph
    truan
    bitri
    uunT1p1.1
    sylbir
end

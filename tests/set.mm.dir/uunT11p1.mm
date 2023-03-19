include "wtru.mm"
include "w3a.mm"
include "wa.mm"
include "3anrot.mm"
include "3anass.mm"
include "truan.mm"
include "3bitri.mm"
include "anidm.mm"
include "bitri.mm"
include "sylbir.mm"

theorem uunT11p1
  let wph: wff ph
  let wps: wff ps
  assume uunT11p1.1: |- ( ( ph /\ T. /\ ph ) -> ps )


  assert |- ( ph -> ps )

  proof
    wph
    wph
    wtru
    wph
    w3a
    #
    wps
    @0
    wph
    wph
    wa
    #
    wph
    @0
    wtru
    wph
    wph
    w3a
    wtru
    @1
    wa
    @1
    wph
    wtru
    wph
    3anrot
    wtru
    wph
    wph
    3anass
    @1
    truan
    3bitri
    wph
    anidm
    bitri
    uunT11p1.1
    sylbir
end

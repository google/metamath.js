include "wa.mm"
include "wtru.mm"
include "w3a.mm"
include "3anrot.mm"
include "3anass.mm"
include "bitri.mm"
include "truan.mm"
include "ancom.mm"
include "bitr4i.mm"
include "sylbir.mm"

theorem uunT12p2
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  assume uunT12p2.1: |- ( ( ph /\ T. /\ ps ) -> ch )


  assert |- ( ( ph /\ ps ) -> ch )

  proof
    wph
    wps
    wa
    #
    wph
    wtru
    wps
    w3a
    #
    wch
    @1
    wps
    wph
    wa
    #
    @0
    @1
    wtru
    @2
    wa
    #
    @2
    @1
    wtru
    wps
    wph
    w3a
    @3
    wph
    wtru
    wps
    3anrot
    wtru
    wps
    wph
    3anass
    bitri
    @2
    truan
    bitri
    wph
    wps
    ancom
    bitr4i
    uunT12p2.1
    sylbir
end

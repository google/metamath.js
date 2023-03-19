include "wa.mm"
include "wtru.mm"
include "w3a.mm"
include "3anrot.mm"
include "3anass.mm"
include "bitr3i.mm"
include "truan.mm"
include "bitri.mm"
include "sylbir.mm"

theorem uunT12p4
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  assume uunT12p4.1: |- ( ( ph /\ ps /\ T. ) -> ch )


  assert |- ( ( ph /\ ps ) -> ch )

  proof
    wph
    wps
    wa
    #
    wph
    wps
    wtru
    w3a
    #
    wch
    @1
    wtru
    @0
    wa
    #
    @0
    @1
    wtru
    wph
    wps
    w3a
    @2
    wtru
    wph
    wps
    3anrot
    wtru
    wph
    wps
    3anass
    bitr3i
    @0
    truan
    bitri
    uunT12p4.1
    sylbir
end

include "wa.mm"
include "wtru.mm"
include "w3a.mm"
include "3anass.mm"
include "truan.mm"
include "bitri.mm"
include "sylbir.mm"

theorem uunT12
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  assume uunT12.1: |- ( ( T. /\ ph /\ ps ) -> ch )


  assert |- ( ( ph /\ ps ) -> ch )

  proof
    wph
    wps
    wa
    #
    wtru
    wph
    wps
    w3a
    #
    wch
    @1
    wtru
    @0
    wa
    @0
    wtru
    wph
    wps
    3anass
    @0
    truan
    bitri
    uunT12.1
    sylbir
end

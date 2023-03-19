include "wa.mm"
include "wtru.mm"
include "w3a.mm"
include "3anrev.mm"
include "3anass.mm"
include "bitri.mm"
include "truan.mm"
include "sylbir.mm"

theorem uunT12p5
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  assume uunT12p5.1: |- ( ( ps /\ ph /\ T. ) -> ch )


  assert |- ( ( ph /\ ps ) -> ch )

  proof
    wph
    wps
    wa
    #
    wps
    wph
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
    wps
    wph
    wtru
    3anrev
    wtru
    wph
    wps
    3anass
    bitri
    @0
    truan
    bitri
    uunT12p5.1
    sylbir
end

include "wa.mm"
include "wtru.mm"
include "w3a.mm"
include "3anass.mm"
include "truan.mm"
include "bitri.mm"
include "ancom.mm"
include "bitr4i.mm"
include "sylbir.mm"

theorem uunT12p1
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  assume uunT12p1.1: |- ( ( T. /\ ps /\ ph ) -> ch )


  assert |- ( ( ph /\ ps ) -> ch )

  proof
    wph
    wps
    wa
    #
    wtru
    wps
    wph
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
    @2
    wtru
    wps
    wph
    3anass
    @2
    truan
    bitri
    wph
    wps
    ancom
    bitr4i
    uunT12p1.1
    sylbir
end

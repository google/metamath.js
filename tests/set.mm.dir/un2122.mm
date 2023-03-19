include "wa.mm"
include "w3a.mm"
include "3anass.mm"
include "anandir.mm"
include "ancom.mm"
include "anabs7.mm"
include "bitri.mm"
include "bitr3i.mm"
include "sylbir.mm"

theorem un2122
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  assume un2122.1: |- ( ( ( ph /\ ps ) /\ ps /\ ps ) -> ch )


  assert |- ( ( ph /\ ps ) -> ch )

  proof
    wph
    wps
    wa
    #
    @0
    wps
    wps
    w3a
    #
    wch
    @1
    @0
    wps
    wps
    wa
    wa
    #
    @0
    @0
    wps
    wps
    3anass
    @2
    @0
    wps
    wa
    #
    @0
    wph
    wps
    wps
    anandir
    @3
    wps
    @0
    wa
    @0
    @0
    wps
    ancom
    wph
    wps
    anabs7
    bitri
    bitr3i
    bitri
    un2122.1
    sylbir
end

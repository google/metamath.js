include "wa.mm"
include "ibar.mm"
include "bitr4d.mm"

theorem bianabs
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  assume bianabs.1: |- ( ph -> ( ps <-> ( ph /\ ch ) ) )


  assert |- ( ph -> ( ps <-> ch ) )

  proof
    wph
    wps
    wph
    wch
    wa
    wch
    bianabs.1
    wph
    wch
    ibar
    bitr4d
end

include "wa.mm"
include "biantrur.mm"
include "bitr4i.mm"

theorem mpbiran
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  assume mpbiran.1: |- ps
  assume mpbiran.2: |- ( ph <-> ( ps /\ ch ) )


  assert |- ( ph <-> ch )

  proof
    wph
    wps
    wch
    wa
    wch
    mpbiran.2
    wps
    wch
    mpbiran.1
    biantrur
    bitr4i
end

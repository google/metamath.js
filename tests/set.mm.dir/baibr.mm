include "baib.mm"
include "bicomd.mm"

theorem baibr
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  assume baib.1: |- ( ph <-> ( ps /\ ch ) )


  assert |- ( ps -> ( ch <-> ph ) )

  proof
    wps
    wph
    wch
    wph
    wps
    wch
    baib.1
    baib
    bicomd
end

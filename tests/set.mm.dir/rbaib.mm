include "rbaibr.mm"
include "bicomd.mm"

theorem rbaib
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  assume baib.1: |- ( ph <-> ( ps /\ ch ) )


  assert |- ( ch -> ( ph <-> ps ) )

  proof
    wch
    wps
    wph
    wph
    wps
    wch
    baib.1
    rbaibr
    bicomd
end

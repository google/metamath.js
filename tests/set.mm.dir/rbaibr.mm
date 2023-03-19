include "wa.mm"
include "iba.mm"
include "syl6bbr.mm"

theorem rbaibr
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  assume baib.1: |- ( ph <-> ( ps /\ ch ) )


  assert |- ( ch -> ( ps <-> ph ) )

  proof
    wch
    wps
    wps
    wch
    wa
    wph
    wch
    wps
    iba
    baib.1
    syl6bbr
end

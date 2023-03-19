include "wa.mm"
include "biimpri.mm"
include "ex.mm"

theorem simplbi2
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  assume simplbi2.1: |- ( ph <-> ( ps /\ ch ) )


  assert |- ( ps -> ( ch -> ph ) )

  proof
    wps
    wch
    wph
    wph
    wps
    wch
    wa
    simplbi2.1
    biimpri
    ex
end

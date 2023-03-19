include "whad.mm"
include "hadcoma.mm"
include "hadcomb.mm"
include "bitri.mm"

theorem hadrot
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch


  assert |- ( hadd ( ph , ps , ch ) <-> hadd ( ps , ch , ph ) )

  proof
    wph
    wps
    wch
    whad
    wps
    wph
    wch
    whad
    wps
    wch
    wph
    whad
    wph
    wps
    wch
    hadcoma
    wps
    wph
    wch
    hadcomb
    bitri
end

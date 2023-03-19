include "wcad.mm"
include "cadcoma.mm"
include "cadcomb.mm"
include "bitri.mm"

theorem cadrot
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch


  assert |- ( cadd ( ph , ps , ch ) <-> cadd ( ps , ch , ph ) )

  proof
    wph
    wps
    wch
    wcad
    wps
    wph
    wch
    wcad
    wps
    wch
    wph
    wcad
    wph
    wps
    wch
    cadcoma
    wps
    wph
    wch
    cadcomb
    bitri
end

include "a1i.mm"
include "impbii.mm"

theorem 2th
  let wph: wff ph
  let wps: wff ps
  assume 2th.1: |- ph
  assume 2th.2: |- ps


  assert |- ( ph <-> ps )

  proof
    wph
    wps
    wps
    wph
    2th.2
    a1i
    wph
    wps
    2th.1
    a1i
    impbii
end

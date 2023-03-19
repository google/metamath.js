include "wn.mm"
include "wi.mm"
include "con1.mm"
include "impbii.mm"

theorem con1b
  let wph: wff ph
  let wps: wff ps


  assert |- ( ( -. ph -> ps ) <-> ( -. ps -> ph ) )

  proof
    wph
    wn
    wps
    wi
    wps
    wn
    wph
    wi
    wph
    wps
    con1
    wps
    wph
    con1
    impbii
end

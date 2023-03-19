include "wn.mm"
include "wi.mm"
include "con2.mm"
include "impbii.mm"

theorem con2b
  let wph: wff ph
  let wps: wff ps


  assert |- ( ( ph -> -. ps ) <-> ( ps -> -. ph ) )

  proof
    wph
    wps
    wn
    wi
    wps
    wph
    wn
    wi
    wph
    wps
    con2
    wps
    wph
    con2
    impbii
end

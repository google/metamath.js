include "wi.mm"
include "wn.mm"
include "con3.mm"
include "con4.mm"
include "impbii.mm"

theorem con34b
  let wph: wff ph
  let wps: wff ps


  assert |- ( ( ph -> ps ) <-> ( -. ps -> -. ph ) )

  proof
    wph
    wps
    wi
    wps
    wn
    wph
    wn
    wi
    wph
    wps
    con3
    wps
    wph
    con4
    impbii
end

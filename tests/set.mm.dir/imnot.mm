include "wn.mm"
include "wi.mm"
include "mtt.mm"
include "bicomd.mm"

theorem imnot
  let wph: wff ph
  let wps: wff ps


  assert |- ( -. ps -> ( ( ph -> ps ) <-> -. ph ) )

  proof
    wps
    wn
    wph
    wn
    wph
    wps
    wi
    wps
    wph
    mtt
    bicomd
end

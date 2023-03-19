include "wi.mm"
include "biimt.mm"
include "bicomd.mm"

theorem pm5.5
  let wph: wff ph
  let wps: wff ps


  assert |- ( ph -> ( ( ph -> ps ) <-> ps ) )

  proof
    wph
    wps
    wph
    wps
    wi
    wph
    wps
    biimt
    bicomd
end

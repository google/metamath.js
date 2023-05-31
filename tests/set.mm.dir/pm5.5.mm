include "wi.mm"
include "biimt.mm"
include "bicomd.mm"

theorem pm5.5
  param wph: wff ph
  param wps: wff ps


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

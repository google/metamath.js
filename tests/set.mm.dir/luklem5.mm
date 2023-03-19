include "wn.mm"
include "wi.mm"
include "luklem3.mm"
include "luklem4.mm"
include "luklem1.mm"

theorem luklem5
  let wph: wff ph
  let wps: wff ps


  assert |- ( ph -> ( ps -> ph ) )

  proof
    wph
    wph
    wn
    wph
    wi
    wph
    wi
    wps
    wph
    wi
    #
    wi
    @0
    wph
    wph
    wph
    wps
    luklem3
    wph
    @0
    luklem4
    luklem1
end

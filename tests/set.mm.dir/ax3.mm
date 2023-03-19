include "wn.mm"
include "wi.mm"
include "luklem2.mm"
include "luklem4.mm"
include "luklem1.mm"

theorem ax3
  let wph: wff ph
  let wps: wff ps


  assert |- ( ( -. ph -> -. ps ) -> ( ps -> ph ) )

  proof
    wph
    wn
    #
    wps
    wn
    wi
    @0
    wph
    wi
    wph
    wi
    wps
    wph
    wi
    #
    wi
    @1
    @0
    wps
    wph
    wph
    luklem2
    wph
    @1
    luklem4
    luklem1
end

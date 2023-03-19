include "wi.mm"
include "jarr.mm"
include "a2d.mm"

theorem loowoz
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch


  assert |- ( ( ( ph -> ps ) -> ( ph -> ch ) ) -> ( ( ps -> ph ) -> ( ps -> ch ) ) )

  proof
    wph
    wps
    wi
    wph
    wch
    wi
    #
    wi
    wps
    wph
    wch
    wph
    wps
    @0
    jarr
    a2d
end

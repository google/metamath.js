include "wi.mm"
include "wa.mm"
include "pm3.21.mm"
include "imim2d.mm"
include "imp.mm"

theorem pm5.31
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch


  assert |- ( ( ch /\ ( ph -> ps ) ) -> ( ph -> ( ps /\ ch ) ) )

  proof
    wch
    wph
    wps
    wi
    wph
    wps
    wch
    wa
    #
    wi
    wch
    wps
    @0
    wph
    wch
    wps
    pm3.21
    imim2d
    imp
end

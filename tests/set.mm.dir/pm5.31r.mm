include "wi.mm"
include "wa.mm"
include "pm3.2.mm"
include "imim2d.mm"
include "imp.mm"

theorem pm5.31r
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch


  assert |- ( ( ch /\ ( ph -> ps ) ) -> ( ph -> ( ch /\ ps ) ) )

  proof
    wch
    wph
    wps
    wi
    wph
    wch
    wps
    wa
    #
    wi
    wch
    wps
    @0
    wph
    wch
    wps
    pm3.2
    imim2d
    imp
end

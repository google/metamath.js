include "wi.mm"
include "wa.mm"
include "pm3.21.mm"
include "imim2d.mm"
include "a2i.mm"

theorem anc2r
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch


  assert |- ( ( ph -> ( ps -> ch ) ) -> ( ph -> ( ps -> ( ch /\ ph ) ) ) )

  proof
    wph
    wps
    wch
    wi
    wps
    wch
    wph
    wa
    #
    wi
    wph
    wch
    @0
    wps
    wph
    wch
    pm3.21
    imim2d
    a2i
end

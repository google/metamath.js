include "wex.mm"
include "19.8a.mm"
include "imim1i.mm"

theorem bj-19.23bit
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x


  assert |- ( ( E. x ph -> ps ) -> ( ph -> ps ) )

  proof
    wph
    wph
    vx
    wex
    wps
    wph
    vx
    19.8a
    imim1i
end

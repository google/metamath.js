include "wn.mm"
include "wi.mm"
include "con2.mm"
include "com12.mm"

theorem bj-con2com
  let wph: wff ph
  let wps: wff ps


  assert |- ( ph -> ( ( ps -> -. ph ) -> -. ps ) )

  proof
    wps
    wph
    wn
    wi
    wph
    wps
    wn
    wps
    wph
    con2
    com12
end

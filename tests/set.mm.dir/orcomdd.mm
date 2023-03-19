include "wo.mm"
include "pm1.4.mm"
include "syl6.mm"

theorem orcomdd
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume orcomdd.1: |- ( ph -> ( ps -> ( ch \/ th ) ) )


  assert |- ( ph -> ( ps -> ( th \/ ch ) ) )

  proof
    wph
    wps
    wch
    wth
    wo
    wth
    wch
    wo
    orcomdd.1
    wch
    wth
    pm1.4
    syl6
end

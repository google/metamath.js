include "wi.mm"
include "w3o.mm"
include "3jao.mm"
include "syl3anc.mm"

theorem 3jaod
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  assume 3jaod.1: |- ( ph -> ( ps -> ch ) )
  assume 3jaod.2: |- ( ph -> ( th -> ch ) )
  assume 3jaod.3: |- ( ph -> ( ta -> ch ) )


  assert |- ( ph -> ( ( ps \/ th \/ ta ) -> ch ) )

  proof
    wph
    wps
    wch
    wi
    wth
    wch
    wi
    wta
    wch
    wi
    wps
    wth
    wta
    w3o
    wch
    wi
    3jaod.1
    3jaod.2
    3jaod.3
    wps
    wch
    wth
    wta
    3jao
    syl3anc
end

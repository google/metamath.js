include "w3o.mm"
include "wi.mm"
include "com3r.mm"
include "3jaoi.mm"
include "com3l.mm"

theorem 3jaodd
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  assume 3jaodd.1: |- ( ph -> ( ps -> ( ch -> et ) ) )
  assume 3jaodd.2: |- ( ph -> ( ps -> ( th -> et ) ) )
  assume 3jaodd.3: |- ( ph -> ( ps -> ( ta -> et ) ) )


  assert |- ( ph -> ( ps -> ( ( ch \/ th \/ ta ) -> et ) ) )

  proof
    wch
    wth
    wta
    w3o
    wph
    wps
    wet
    wch
    wph
    wps
    wet
    wi
    wi
    wth
    wta
    wph
    wps
    wch
    wet
    3jaodd.1
    com3r
    wph
    wps
    wth
    wet
    3jaodd.2
    com3r
    wph
    wps
    wta
    wet
    3jaodd.3
    com3r
    3jaoi
    com3l
end

include "wo.mm"
include "or32.mm"
include "syl6ibr.mm"

theorem or32dd
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  assume or32dd.1: |- ( ph -> ( ps -> ( ( ch \/ th ) \/ ta ) ) )


  assert |- ( ph -> ( ps -> ( ( ch \/ ta ) \/ th ) ) )

  proof
    wph
    wps
    wch
    wth
    wo
    wta
    wo
    wch
    wta
    wo
    wth
    wo
    or32dd.1
    wch
    wta
    wth
    or32
    syl6ibr
end

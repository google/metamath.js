include "wa.mm"
include "wi.mm"
include "adantrd.mm"
include "adantld.mm"
include "jaoi.mm"

theorem jaoa
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  assume jaao.1: |- ( ph -> ( ps -> ch ) )
  assume jaao.2: |- ( th -> ( ta -> ch ) )


  assert |- ( ( ph \/ th ) -> ( ( ps /\ ta ) -> ch ) )

  proof
    wph
    wps
    wta
    wa
    wch
    wi
    wth
    wph
    wps
    wch
    wta
    jaao.1
    adantrd
    wth
    wta
    wch
    wps
    jaao.2
    adantld
    jaoi
end

include "wi.mm"
include "wo.mm"
include "jao.mm"
include "3imp.mm"
include "syl3an.mm"

theorem jaoded
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  assume jaoded.1: |- ( ph -> ( ps -> ch ) )
  assume jaoded.2: |- ( th -> ( ta -> ch ) )
  assume jaoded.3: |- ( et -> ( ps \/ ta ) )


  assert |- ( ( ph /\ th /\ et ) -> ch )

  proof
    wph
    wps
    wch
    wi
    #
    wth
    wta
    wch
    wi
    #
    wet
    wps
    wta
    wo
    #
    wch
    jaoded.1
    jaoded.2
    jaoded.3
    @0
    @1
    @2
    wch
    wps
    wch
    wta
    jao
    3imp
    syl3an
end

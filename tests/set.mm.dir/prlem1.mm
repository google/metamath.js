include "wa.mm"
include "wo.mm"
include "wi.mm"
include "biimprd.mm"
include "adantld.mm"
include "pm2.21d.mm"
include "adantrd.mm"
include "jaao.mm"
include "ex.mm"

theorem prlem1
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  assume prlem1.1: |- ( ph -> ( et <-> ch ) )
  assume prlem1.2: |- ( ps -> -. th )


  assert |- ( ph -> ( ps -> ( ( ( ps /\ ch ) \/ ( th /\ ta ) ) -> et ) ) )

  proof
    wph
    wps
    wps
    wch
    wa
    #
    wth
    wta
    wa
    #
    wo
    wet
    wi
    wph
    @0
    wet
    wps
    @1
    wph
    wch
    wet
    wps
    wph
    wet
    wch
    prlem1.1
    biimprd
    adantld
    wps
    wth
    wet
    wta
    wps
    wth
    wet
    prlem1.2
    pm2.21d
    adantrd
    jaao
    ex
end

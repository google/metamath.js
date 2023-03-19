include "wn.mm"
include "w3o.mm"
include "wi.mm"
include "idd.mm"
include "pm2.21.mm"
include "3jaao.mm"
include "3anidm12.mm"

theorem 3ornot23
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch


  assert |- ( ( -. ph /\ -. ps ) -> ( ( ch \/ ph \/ ps ) -> ch ) )

  proof
    wph
    wn
    #
    wps
    wn
    #
    wch
    wph
    wps
    w3o
    wch
    wi
    @0
    wch
    wch
    @0
    wph
    @1
    wps
    @0
    wch
    idd
    wph
    wch
    pm2.21
    wps
    wch
    pm2.21
    3jaao
    3anidm12
end

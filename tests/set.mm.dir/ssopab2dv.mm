include "wi.mm"
include "wal.mm"
include "copab.mm"
include "wss.mm"
include "alrimivv.mm"
include "ssopab2.mm"
include "syl.mm"

theorem ssopab2dv
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let vy: setvar y
  assume ssopab2dv.1: |- ( ph -> ( ps -> ch ) )

  disjoint ph x
  disjoint ph y
  assert |- ( ph -> { <. x , y >. | ps } C_ { <. x , y >. | ch } )

  proof
    wph
    wps
    wch
    wi
    #
    vy
    wal
    vx
    wal
    wps
    vx
    vy
    copab
    wch
    vx
    vy
    copab
    wss
    wph
    @0
    vx
    vy
    ssopab2dv.1
    alrimivv
    wps
    wch
    vx
    vy
    ssopab2
    syl
end

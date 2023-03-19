include "wal.mm"
include "wi.mm"
include "wn.mm"
include "alrimih.mm"
include "hbnt.mm"
include "syl.mm"

theorem hbnd
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  assume hbnd.1: |- ( ph -> A. x ph )
  assume hbnd.2: |- ( ph -> ( ps -> A. x ps ) )


  assert |- ( ph -> ( -. ps -> A. x -. ps ) )

  proof
    wph
    wps
    wps
    vx
    wal
    wi
    #
    vx
    wal
    wps
    wn
    #
    @1
    vx
    wal
    wi
    wph
    @0
    vx
    hbnd.1
    hbnd.2
    alrimih
    wps
    vx
    hbnt
    syl
end

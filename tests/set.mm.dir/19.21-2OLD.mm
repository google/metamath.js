include "wi.mm"
include "wal.mm"
include "19.21OLD.mm"
include "albii.mm"
include "bitri.mm"

theorem 19.21-2OLD
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  assume 19.21-2OLD.1: |- nfOLD x ph
  assume 19.21-2OLD.2: |- nfOLD y ph


  assert |- ( A. x A. y ( ph -> ps ) <-> ( ph -> A. x A. y ps ) )

  proof
    wph
    wps
    wi
    vy
    wal
    #
    vx
    wal
    wph
    wps
    vy
    wal
    #
    wi
    #
    vx
    wal
    wph
    @1
    vx
    wal
    wi
    @0
    @2
    vx
    wph
    wps
    vy
    19.21-2OLD.2
    19.21OLD
    albii
    wph
    @1
    vx
    19.21-2OLD.1
    19.21OLD
    bitri
end

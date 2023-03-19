include "wal.mm"
include "weq.mm"
include "biimpd.mm"
include "cbvalivw.mm"
include "alimi.mm"
include "ax-5.mm"
include "wi.mm"
include "biimprd.mm"
include "equcoms.mm"
include "spimvw.mm"
include "3syl.mm"

theorem alcomiw
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume alcomiw.1: |- ( y = z -> ( ph <-> ps ) )

  disjoint y z
  disjoint x y
  disjoint ph z
  disjoint ps y
  assert |- ( A. x A. y ph -> A. y A. x ph )

  proof
    wph
    vy
    wal
    #
    vx
    wal
    wps
    vz
    wal
    #
    vx
    wal
    #
    @2
    vy
    wal
    wph
    vx
    wal
    #
    vy
    wal
    @0
    @1
    vx
    wph
    wps
    vy
    vz
    vy
    vz
    weq
    #
    wph
    wps
    alcomiw.1
    biimpd
    cbvalivw
    alimi
    @2
    vy
    ax-5
    @2
    @3
    vy
    @1
    wph
    vx
    wps
    wph
    vz
    vy
    wps
    wph
    wi
    vy
    vz
    @4
    wph
    wps
    alcomiw.1
    biimprd
    equcoms
    spimvw
    alimi
    alimi
    3syl
end

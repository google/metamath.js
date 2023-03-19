include "weq.mm"
include "wal.mm"
include "aev-o.mm"
include "ax-c16.mm"
include "biidd.mm"
include "dral1-o.mm"
include "biimprd.mm"
include "sylsyld.mm"

theorem axc16g-o
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z

  disjoint x y
  assert |- ( A. x x = y -> ( ph -> A. z ph ) )

  proof
    vx
    vy
    weq
    vx
    wal
    vz
    vx
    weq
    vz
    wal
    #
    wph
    wph
    vx
    wal
    #
    wph
    vz
    wal
    #
    vx
    vy
    vz
    vz
    vx
    aev-o
    wph
    vx
    vy
    ax-c16
    @0
    @2
    @1
    wph
    wph
    vz
    vx
    @0
    wph
    biidd
    dral1-o
    biimprd
    sylsyld
end

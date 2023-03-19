include "weq.mm"
include "wal.mm"
include "aev.mm"
include "axc16ALT.mm"
include "biidd.mm"
include "dral1.mm"
include "biimprd.mm"
include "sylsyld.mm"

theorem axc16gALT
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
    vx
    vz
    aev
    wph
    vx
    vy
    axc16ALT
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
    dral1
    biimprd
    sylsyld
end

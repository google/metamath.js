include "weq.mm"
include "wsb.mm"
include "wa.mm"
include "wex.mm"
include "nfsb.mm"
include "sbequ.mm"
include "equsexv.mm"
include "bicomi.mm"

theorem sb10f
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume sb10f.1: |- F/ x ph

  disjoint x y
  assert |- ( [ y / z ] ph <-> E. x ( x = y /\ [ x / z ] ph ) )

  proof
    vx
    vy
    weq
    wph
    vz
    vx
    wsb
    #
    wa
    vx
    wex
    wph
    vz
    vy
    wsb
    #
    @0
    @1
    vx
    vy
    wph
    vz
    vy
    vx
    sb10f.1
    nfsb
    wph
    vx
    vy
    vz
    sbequ
    equsexv
    bicomi
end

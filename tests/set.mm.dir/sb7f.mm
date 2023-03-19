include "wsb.mm"
include "weq.mm"
include "wa.mm"
include "wex.mm"
include "sb5f.mm"
include "sbbii.mm"
include "sbco2.mm"
include "sb5.mm"
include "3bitr3i.mm"

theorem sb7f
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume sb7f.1: |- F/ z ph

  disjoint y z
  assert |- ( [ y / x ] ph <-> E. z ( z = y /\ E. x ( x = z /\ ph ) ) )

  proof
    wph
    vx
    vz
    wsb
    #
    vz
    vy
    wsb
    vx
    vz
    weq
    wph
    wa
    vx
    wex
    #
    vz
    vy
    wsb
    wph
    vx
    vy
    wsb
    vz
    vy
    weq
    @1
    wa
    vz
    wex
    @0
    @1
    vz
    vy
    wph
    vx
    vz
    sb7f.1
    sb5f
    sbbii
    wph
    vx
    vy
    vz
    sb7f.1
    sbco2
    @1
    vz
    vy
    sb5
    3bitr3i
end

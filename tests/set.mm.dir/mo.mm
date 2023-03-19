include "weq.mm"
include "wi.mm"
include "wal.mm"
include "wex.mm"
include "wmo.mm"
include "wsb.mm"
include "wa.mm"
include "mo2.mm"
include "mo3.mm"
include "bitr3i.mm"

theorem mo
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  assume mo.1: |- F/ y ph

  disjoint x y
  assert |- ( E. y A. x ( ph -> x = y ) <-> A. x A. y ( ( ph /\ [ y / x ] ph ) -> x = y ) )

  proof
    wph
    vx
    vy
    weq
    #
    wi
    vx
    wal
    vy
    wex
    wph
    vx
    wmo
    wph
    wph
    vx
    vy
    wsb
    wa
    @0
    wi
    vy
    wal
    vx
    wal
    wph
    vx
    vy
    mo.1
    mo2
    wph
    vx
    vy
    mo.1
    mo3
    bitr3i
end

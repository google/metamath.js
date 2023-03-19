include "wsb.mm"
include "weq.mm"
include "wi.mm"
include "wal.mm"
include "wa.mm"
include "wex.mm"
include "bj-sb6.mm"
include "sb56.mm"
include "bitr4i.mm"

theorem bj-sb5
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y

  disjoint x y
  assert |- ( [ y / x ] ph <-> E. x ( x = y /\ ph ) )

  proof
    wph
    vx
    vy
    wsb
    vx
    vy
    weq
    #
    wph
    wi
    vx
    wal
    @0
    wph
    wa
    vx
    wex
    wph
    vx
    vy
    bj-sb6
    wph
    vx
    vy
    sb56
    bitr4i
end

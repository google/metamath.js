include "wsb.mm"
include "weq.mm"
include "wa.mm"
include "wex.mm"
include "wi.mm"
include "wal.mm"
include "sb1.mm"
include "sb56.mm"
include "sylib.mm"

theorem bj-sb4v
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y

  disjoint x y
  assert |- ( [ y / x ] ph -> A. x ( x = y -> ph ) )

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
    wa
    vx
    wex
    @0
    wph
    wi
    vx
    wal
    wph
    vx
    vy
    sb1
    wph
    vx
    vy
    sb56
    sylib
end

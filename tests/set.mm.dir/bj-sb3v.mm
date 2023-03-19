include "weq.mm"
include "wa.mm"
include "wex.mm"
include "wi.mm"
include "wal.mm"
include "wsb.mm"
include "sb56.mm"
include "bj-sb2v.mm"
include "sylbi.mm"

theorem bj-sb3v
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y

  disjoint x y
  assert |- ( E. x ( x = y /\ ph ) -> [ y / x ] ph )

  proof
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
    wsb
    wph
    vx
    vy
    sb56
    wph
    vx
    vy
    bj-sb2v
    sylbi
end

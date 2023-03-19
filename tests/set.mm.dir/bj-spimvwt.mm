include "weq.mm"
include "wi.mm"
include "wal.mm"
include "wex.mm"
include "bj-alequexv.mm"
include "19.36v.mm"
include "sylib.mm"

theorem bj-spimvwt
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y

  disjoint x y
  disjoint ps x
  assert |- ( A. x ( x = y -> ( ph -> ps ) ) -> ( A. x ph -> ps ) )

  proof
    vx
    vy
    weq
    wph
    wps
    wi
    #
    wi
    vx
    wal
    @0
    vx
    wex
    wph
    vx
    wal
    wps
    wi
    @0
    vx
    vy
    bj-alequexv
    wph
    wps
    vx
    19.36v
    sylib
end

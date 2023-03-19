include "wex.mm"
include "wrex.mm"
include "rexex.mm"
include "eximi.mm"
include "3syl.mm"
include "nfexd.mm"
include "19.9d.mm"
include "mpd.mm"

theorem 19.9d2rf
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  assume 19.9d2rf.0: |- F/ y ph
  assume 19.9d2rf.1: |- ( ph -> F/ x ps )
  assume 19.9d2rf.2: |- ( ph -> F/ y ps )
  assume 19.9d2rf.3: |- ( ph -> E. x e. A E. y e. B ps )


  assert |- ( ph -> ps )

  proof
    wph
    wps
    vy
    wex
    #
    wps
    wph
    @0
    vx
    wex
    #
    @0
    wph
    wps
    vy
    cB
    wrex
    #
    vx
    cA
    wrex
    @2
    vx
    wex
    @1
    19.9d2rf.3
    @2
    vx
    cA
    rexex
    @2
    @0
    vx
    wps
    vy
    cB
    rexex
    eximi
    3syl
    @0
    wph
    vx
    wph
    wps
    vx
    vy
    19.9d2rf.0
    19.9d2rf.1
    nfexd
    19.9d
    mpd
    wps
    wph
    vy
    19.9d2rf.2
    19.9d
    mpd
end

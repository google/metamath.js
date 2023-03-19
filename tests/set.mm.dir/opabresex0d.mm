include "cv.mm"
include "wbr.mm"
include "wcel.mm"
include "wa.mm"
include "wi.mm"
include "wal.mm"
include "copab.mm"
include "cvv.mm"
include "jca.mm"
include "ex.mm"
include "alrimivv.mm"
include "elexd.mm"
include "cab.mm"
include "opabex3d.mm"
include "opabbrex.mm"
include "syl2anc.mm"

theorem opabresex0d
  let wph: wff ph
  let wps: wff ps
  let wth: wff th
  let vx: setvar x
  let vy: setvar y
  let cC: class C
  let cR: class R
  let cV: class V
  let cW: class W
  let vk: setvar k
  assume opabresex0d.x: |- ( ( ph /\ x R y ) -> x e. C )
  assume opabresex0d.t: |- ( ( ph /\ x R y ) -> th )
  assume opabresex0d.y: |- ( ( ph /\ x e. C ) -> { y | th } e. V )
  assume opabresex0d.c: |- ( ph -> C e. W )

  disjoint C x
  disjoint C y
  disjoint x y
  disjoint ph x
  disjoint ph y
  disjoint k x
  assert |- ( ph -> { <. x , y >. | ( x R y /\ ps ) } e. _V )

  proof
    wph
    vx
    cv
    #
    vy
    cv
    cR
    wbr
    #
    @0
    cC
    wcel
    #
    wth
    wa
    #
    wi
    #
    vy
    wal
    vx
    wal
    @3
    vx
    vy
    copab
    cvv
    wcel
    @1
    wps
    wa
    vx
    vy
    copab
    cvv
    wcel
    wph
    @4
    vx
    vy
    wph
    @1
    @3
    wph
    @1
    wa
    @2
    wth
    opabresex0d.x
    opabresex0d.t
    jca
    ex
    alrimivv
    wph
    wth
    vx
    vy
    cC
    wph
    cC
    cW
    opabresex0d.c
    elexd
    wph
    @2
    wa
    wth
    vy
    cab
    cV
    opabresex0d.y
    elexd
    opabex3d
    @3
    wps
    vx
    vy
    cR
    cvv
    opabbrex
    syl2anc
end

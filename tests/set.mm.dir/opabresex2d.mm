include "cv.mm"
include "cfv.mm"
include "wbr.mm"
include "wi.mm"
include "wal.mm"
include "copab.mm"
include "wcel.mm"
include "wa.mm"
include "cvv.mm"
include "ex.mm"
include "alrimivv.mm"
include "opabbrex.mm"
include "syl2anc.mm"

theorem opabresex2d
  let wph: wff ph
  let wps: wff ps
  let wth: wff th
  let vx: setvar x
  let vy: setvar y
  let cG: class G
  let cV: class V
  let cW: class W
  assume opabresex2d.1: |- ( ( ph /\ x ( W ` G ) y ) -> ps )
  assume opabresex2d.2: |- ( ph -> { <. x , y >. | ps } e. V )

  disjoint ph x
  disjoint ph y
  assert |- ( ph -> { <. x , y >. | ( x ( W ` G ) y /\ th ) } e. _V )

  proof
    wph
    vx
    cv
    vy
    cv
    cG
    cW
    cfv
    #
    wbr
    #
    wps
    wi
    #
    vy
    wal
    vx
    wal
    wps
    vx
    vy
    copab
    cV
    wcel
    @1
    wth
    wa
    vx
    vy
    copab
    cvv
    wcel
    wph
    @2
    vx
    vy
    wph
    @1
    wps
    opabresex2d.1
    ex
    alrimivv
    opabresex2d.2
    wps
    wth
    vx
    vy
    @0
    cV
    opabbrex
    syl2anc
end

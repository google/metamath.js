include "cbs.mm"
include "cfv.mm"
include "eqidd.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "cplusg.mm"
include "oveqdr.mm"
include "cmulr.mm"
include "abvpropd.mm"

theorem abvpropd2
  let wph: wff ph
  let cK: class K
  let cL: class L
  let vx: setvar x
  let vy: setvar y
  assume abvpropd2.1: |- ( ph -> ( Base ` K ) = ( Base ` L ) )
  assume abvpropd2.2: |- ( ph -> ( +g ` K ) = ( +g ` L ) )
  assume abvpropd2.3: |- ( ph -> ( .r ` K ) = ( .r ` L ) )


  assert |- ( ph -> ( AbsVal ` K ) = ( AbsVal ` L ) )

  proof
    wph
    vx
    vy
    cK
    cbs
    cfv
    #
    cK
    cL
    wph
    @0
    eqidd
    abvpropd2.1
    wph
    vx
    cv
    @0
    wcel
    vy
    cv
    @0
    wcel
    wa
    #
    vx
    vy
    cK
    cplusg
    cfv
    cL
    cplusg
    cfv
    abvpropd2.2
    oveqdr
    wph
    @1
    vx
    vy
    cK
    cmulr
    cfv
    cL
    cmulr
    cfv
    abvpropd2.3
    oveqdr
    abvpropd
end

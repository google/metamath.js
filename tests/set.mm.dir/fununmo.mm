include "cun.mm"
include "wfun.mm"
include "cv.mm"
include "wbr.mm"
include "wmo.mm"
include "funmo.mm"
include "wo.mm"
include "orc.mm"
include "brun.mm"
include "sylibr.mm"
include "moimi.mm"
include "syl.mm"

theorem fununmo
  let vx: setvar x
  let vy: setvar y
  let cF: class F
  let cG: class G

  disjoint x y
  disjoint F y
  disjoint G y
  assert |- ( Fun ( F u. G ) -> E* y x F y )

  proof
    cF
    cG
    cun
    #
    wfun
    vx
    cv
    #
    vy
    cv
    #
    @0
    wbr
    #
    vy
    wmo
    @1
    @2
    cF
    wbr
    #
    vy
    wmo
    vy
    @1
    @0
    funmo
    @4
    @3
    vy
    @4
    @4
    @1
    @2
    cG
    wbr
    #
    wo
    @3
    @4
    @5
    orc
    @1
    @2
    cF
    cG
    brun
    sylibr
    moimi
    syl
end

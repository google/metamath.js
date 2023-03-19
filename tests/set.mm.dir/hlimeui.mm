include "cv.mm"
include "chli.mm"
include "wbr.mm"
include "cvv.mm"
include "wrex.mm"
include "wreu.mm"
include "wex.mm"
include "weu.mm"
include "hlimreui.mm"
include "rexv.mm"
include "reuv.mm"
include "3bitr3i.mm"

theorem hlimeui
  let vx: setvar x
  let cF: class F
  let vy: setvar y
  let cH: class H

  disjoint F x
  disjoint x y
  disjoint F y
  disjoint H x
  disjoint H y
  assert |- ( E. x F ~~>v x <-> E! x F ~~>v x )

  proof
    cF
    vx
    cv
    chli
    wbr
    #
    vx
    cvv
    wrex
    @0
    vx
    cvv
    wreu
    @0
    vx
    wex
    @0
    vx
    weu
    vx
    cF
    cvv
    hlimreui
    @0
    vx
    rexv
    @0
    vx
    reuv
    3bitr3i
end

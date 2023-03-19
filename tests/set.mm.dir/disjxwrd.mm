include "cword.mm"
include "cv.mm"
include "cc0.mm"
include "cop.mm"
include "csubstr.mm"
include "co.mm"
include "invdisjrab.mm"

theorem disjxwrd
  let vx: setvar x
  let vy: setvar y
  let cN: class N
  let cV: class V
  let cW: class W

  disjoint N y
  disjoint V x
  disjoint x y
  assert |- Disj_ y e. W { x e. Word V | ( x substr <. 0 , N >. ) = y }

  proof
    vx
    vy
    cW
    cV
    cword
    vx
    cv
    cc0
    cN
    cop
    csubstr
    co
    invdisjrab
end

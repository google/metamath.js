include "cword.mm"
include "cv.mm"
include "cpfx.mm"
include "co.mm"
include "invdisjrab.mm"

theorem disjwrdpfx
  let vx: setvar x
  let vy: setvar y
  let cN: class N
  let cV: class V
  let cW: class W
  let vk: setvar k

  disjoint N y
  disjoint V x
  disjoint x y
  disjoint k x
  assert |- Disj_ y e. W { x e. Word V | ( x prefix N ) = y }

  proof
    vx
    vy
    cW
    cV
    cword
    vx
    cv
    cN
    cpfx
    co
    invdisjrab
end

include "cphl.mm"
include "wcel.mm"
include "clvec.mm"
include "clmod.mm"
include "phllvec.mm"
include "lveclmod.mm"
include "syl.mm"

theorem phllmod
  let cW: class W
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cG: class G
  let c.xi: class .,
  let c.as: class .*
  let cF: class F
  let cK: class K
  let c.0: class .0.
  let c.x: class .x.
  let cV: class V
  let cZ: class Z


  assert |- ( W e. PreHil -> W e. LMod )

  proof
    cW
    cphl
    wcel
    cW
    clvec
    wcel
    cW
    clmod
    wcel
    cW
    phllvec
    cW
    lveclmod
    syl
end

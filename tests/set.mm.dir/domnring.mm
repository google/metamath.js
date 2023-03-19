include "cdomn.mm"
include "wcel.mm"
include "cnzr.mm"
include "crg.mm"
include "domnnzr.mm"
include "nzrring.mm"
include "syl.mm"

theorem domnring
  let cR: class R
  let vx: setvar x
  let vy: setvar y
  let c.0: class .0.
  let cB: class B
  let c.x: class .x.
  let cX: class X
  let cY: class Y


  assert |- ( R e. Domn -> R e. Ring )

  proof
    cR
    cdomn
    wcel
    cR
    cnzr
    wcel
    cR
    crg
    wcel
    cR
    domnnzr
    cR
    nzrring
    syl
end

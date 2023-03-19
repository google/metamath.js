include "cofr.mm"
include "nfcv.mm"

theorem nfofr
  let vx: setvar x
  let cR: class R
  let vf: setvar f
  let vg: setvar g
  let cS: class S
  assume nfof.1: |- F/_ x R

  disjoint R x
  disjoint f g
  disjoint f x
  disjoint R f
  disjoint g x
  disjoint R g
  disjoint S f
  disjoint S g
  disjoint S x
  assert |- F/_ x oR R

  proof
    vx
    cR
    cofr
    nfcv
end

include "wcel.mm"
include "cvv.mm"
include "elbasov.mm"
include "simpld.mm"

theorem strov2rcl
  let cB: class B
  let cR: class R
  let cS: class S
  let cF: class F
  let cI: class I
  let cX: class X
  assume strov2rcl.s: |- S = ( I F R )
  assume strov2rcl.b: |- B = ( Base ` S )
  assume strov2rcl.f: |- Rel dom F


  assert |- ( X e. B -> I e. _V )

  proof
    cX
    cB
    wcel
    cI
    cvv
    wcel
    cR
    cvv
    wcel
    cX
    cB
    cS
    cF
    cI
    cR
    strov2rcl.f
    strov2rcl.s
    strov2rcl.b
    elbasov
    simpld
end

include "cv.mm"
include "unitcl.mm"
include "ssriv.mm"

theorem unitss
  let cB: class B
  let cR: class R
  let cU: class U
  let vx: setvar x
  let cX: class X
  assume unitcl.1: |- B = ( Base ` R )
  assume unitcl.2: |- U = ( Unit ` R )


  assert |- U C_ B

  proof
    vx
    cU
    cB
    cB
    cR
    cU
    vx
    cv
    unitcl.1
    unitcl.2
    unitcl
    ssriv
end

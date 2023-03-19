include "cv.mm"
include "atbase.mm"
include "ssriv.mm"

theorem atssbase
  let cA: class A
  let cB: class B
  let cK: class K
  let vx: setvar x
  assume atombase.b: |- B = ( Base ` K )
  assume atombase.a: |- A = ( Atoms ` K )


  assert |- A C_ B

  proof
    vx
    cA
    cB
    cA
    cB
    vx
    cv
    cK
    atombase.b
    atombase.a
    atbase
    ssriv
end

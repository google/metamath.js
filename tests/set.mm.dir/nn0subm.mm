include "cn0.mm"
include "cv.mm"
include "nn0cn.mm"
include "nn0addcl.mm"
include "0nn0.mm"
include "cnsubmlem.mm"

theorem nn0subm
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cR: class R


  assert |- NN0 e. ( SubMnd ` CCfld )

  proof
    vx
    vy
    cn0
    vx
    cv
    #
    nn0cn
    @0
    vy
    cv
    nn0addcl
    0nn0
    cnsubmlem
end

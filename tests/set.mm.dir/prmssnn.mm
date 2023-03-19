include "cprime.mm"
include "cn.mm"
include "cv.mm"
include "prmnn.mm"
include "ssriv.mm"

theorem prmssnn
  let vx: setvar x


  assert |- Prime C_ NN

  proof
    vx
    cprime
    cn
    vx
    cv
    prmnn
    ssriv
end

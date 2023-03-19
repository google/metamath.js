include "cprime.mm"
include "cn.mm"
include "wss.mm"
include "cv.mm"
include "clt.mm"
include "wbr.mm"
include "wrex.mm"
include "wral.mm"
include "cen.mm"
include "prmnn.mm"
include "ssriv.mm"
include "prmunb.mm"
include "rgen.mm"
include "unben.mm"
include "mp2an.mm"

theorem prminf
  let vn: setvar n
  let vp: setvar p


  assert |- Prime ~~ NN

  proof
    cprime
    cn
    wss
    vn
    cv
    #
    vp
    cv
    #
    clt
    wbr
    vp
    cprime
    wrex
    #
    vn
    cn
    wral
    cprime
    cn
    cen
    wbr
    vp
    cprime
    cn
    @1
    prmnn
    ssriv
    @2
    vn
    cn
    @0
    vp
    prmunb
    rgen
    cprime
    vn
    vp
    unben
    mp2an
end

include "cc0.mm"
include "cabs.mm"
include "cfv.mm"
include "ccj.mm"
include "cmul.mm"
include "co.mm"
include "csqrt.mm"
include "cc.mm"
include "wcel.mm"
include "wceq.mm"
include "0cn.mm"
include "absval.mm"
include "ax-mp.mm"
include "cjcli.mm"
include "mul02i.mm"
include "fveq2i.mm"
include "sqrt0.mm"
include "3eqtri.mm"

theorem abs0



  assert |- ( abs ` 0 ) = 0

  proof
    cc0
    cabs
    cfv
    #
    cc0
    cc0
    ccj
    cfv
    #
    cmul
    co
    #
    csqrt
    cfv
    #
    cc0
    csqrt
    cfv
    cc0
    cc0
    cc
    wcel
    @0
    @3
    wceq
    0cn
    cc0
    absval
    ax-mp
    @2
    cc0
    csqrt
    @1
    cc0
    0cn
    cjcli
    mul02i
    fveq2i
    sqrt0
    3eqtri
end

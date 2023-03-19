include "c0v.mm"
include "cno.mm"
include "cfv.mm"
include "csp.mm"
include "co.mm"
include "csqrt.mm"
include "cc0.mm"
include "chil.mm"
include "wcel.mm"
include "wceq.mm"
include "ax-hv0cl.mm"
include "normval.mm"
include "ax-mp.mm"
include "hi01.mm"
include "fveq2d.mm"
include "sqrt0.mm"
include "3eqtri.mm"

theorem norm0



  assert |- ( normh ` 0h ) = 0

  proof
    c0v
    cno
    cfv
    #
    c0v
    c0v
    csp
    co
    #
    csqrt
    cfv
    #
    cc0
    csqrt
    cfv
    #
    cc0
    c0v
    chil
    wcel
    #
    @0
    @2
    wceq
    ax-hv0cl
    c0v
    normval
    ax-mp
    @4
    @2
    @3
    wceq
    ax-hv0cl
    @4
    @1
    cc0
    csqrt
    c0v
    hi01
    fveq2d
    ax-mp
    sqrt0
    3eqtri
end

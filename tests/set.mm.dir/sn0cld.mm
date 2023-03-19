include "c0.mm"
include "cpw.mm"
include "ccld.mm"
include "cfv.mm"
include "csn.mm"
include "cvv.mm"
include "wcel.mm"
include "wceq.mm"
include "0ex.mm"
include "discld.mm"
include "ax-mp.mm"
include "pw0.mm"
include "fveq2i.mm"
include "3eqtr3i.mm"

theorem sn0cld
  let cA: class A
  let vx: setvar x
  let cV: class V


  assert |- ( Clsd ` { (/) } ) = { (/) }

  proof
    c0
    cpw
    #
    ccld
    cfv
    #
    @0
    c0
    csn
    #
    ccld
    cfv
    @2
    c0
    cvv
    wcel
    @1
    @0
    wceq
    0ex
    c0
    cvv
    discld
    ax-mp
    @0
    @2
    ccld
    pw0
    fveq2i
    pw0
    3eqtr3i
end

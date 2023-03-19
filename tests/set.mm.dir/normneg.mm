include "chil.mm"
include "wcel.mm"
include "c0v.mm"
include "cmv.mm"
include "co.mm"
include "cno.mm"
include "cfv.mm"
include "c1.mm"
include "cneg.mm"
include "csm.mm"
include "wceq.mm"
include "ax-hv0cl.mm"
include "normsub.mm"
include "mpan.mm"
include "hv2neg.mm"
include "fveq2d.mm"
include "hvsub0.mm"
include "3eqtr3d.mm"

theorem normneg
  let cA: class A


  assert |- ( A e. ~H -> ( normh ` ( -u 1 .h A ) ) = ( normh ` A ) )

  proof
    cA
    chil
    wcel
    #
    c0v
    cA
    cmv
    co
    #
    cno
    cfv
    #
    cA
    c0v
    cmv
    co
    #
    cno
    cfv
    #
    c1
    cneg
    cA
    csm
    co
    #
    cno
    cfv
    cA
    cno
    cfv
    c0v
    chil
    wcel
    @0
    @2
    @4
    wceq
    ax-hv0cl
    c0v
    cA
    normsub
    mpan
    @0
    @1
    @5
    cno
    cA
    hv2neg
    fveq2d
    @0
    @3
    cA
    cno
    cA
    hvsub0
    fveq2d
    3eqtr3d
end

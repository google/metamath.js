include "chil.mm"
include "wcel.mm"
include "c0v.mm"
include "csp.mm"
include "co.mm"
include "ccj.mm"
include "cfv.mm"
include "cc0.mm"
include "wceq.mm"
include "ax-hv0cl.mm"
include "ax-his1.mm"
include "mpan2.mm"
include "hi01.mm"
include "fveq2d.mm"
include "cj0.mm"
include "syl6eq.mm"
include "eqtrd.mm"

theorem hi02
  let cA: class A


  assert |- ( A e. ~H -> ( A .ih 0h ) = 0 )

  proof
    cA
    chil
    wcel
    #
    cA
    c0v
    csp
    co
    #
    c0v
    cA
    csp
    co
    #
    ccj
    cfv
    #
    cc0
    @0
    c0v
    chil
    wcel
    @1
    @3
    wceq
    ax-hv0cl
    cA
    c0v
    ax-his1
    mpan2
    @0
    @3
    cc0
    ccj
    cfv
    cc0
    @0
    @2
    cc0
    ccj
    cA
    hi01
    fveq2d
    cj0
    syl6eq
    eqtrd
end

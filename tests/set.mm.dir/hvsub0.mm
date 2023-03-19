include "chil.mm"
include "wcel.mm"
include "c0v.mm"
include "cmv.mm"
include "co.mm"
include "cva.mm"
include "c1.mm"
include "cneg.mm"
include "csm.mm"
include "wceq.mm"
include "ax-hv0cl.mm"
include "hvsubval.mm"
include "mpan2.mm"
include "cc.mm"
include "neg1cn.mm"
include "hvmul0.mm"
include "ax-mp.mm"
include "oveq2i.mm"
include "syl6eq.mm"
include "ax-hvaddid.mm"
include "eqtrd.mm"

theorem hvsub0
  let cA: class A


  assert |- ( A e. ~H -> ( A -h 0h ) = A )

  proof
    cA
    chil
    wcel
    #
    cA
    c0v
    cmv
    co
    #
    cA
    c0v
    cva
    co
    #
    cA
    @0
    @1
    cA
    c1
    cneg
    #
    c0v
    csm
    co
    #
    cva
    co
    #
    @2
    @0
    c0v
    chil
    wcel
    @1
    @5
    wceq
    ax-hv0cl
    cA
    c0v
    hvsubval
    mpan2
    @4
    c0v
    cA
    cva
    @3
    cc
    wcel
    @4
    c0v
    wceq
    neg1cn
    @3
    hvmul0
    ax-mp
    oveq2i
    syl6eq
    cA
    ax-hvaddid
    eqtrd
end

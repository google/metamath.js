include "chil.mm"
include "wcel.mm"
include "c0v.mm"
include "cmv.mm"
include "co.mm"
include "c1.mm"
include "cneg.mm"
include "csm.mm"
include "cva.mm"
include "wceq.mm"
include "ax-hv0cl.mm"
include "hvsubval.mm"
include "mpan.mm"
include "cc.mm"
include "neg1cn.mm"
include "hvmulcl.mm"
include "hvaddid2.mm"
include "syl.mm"
include "eqtrd.mm"

theorem hv2neg
  let cA: class A


  assert |- ( A e. ~H -> ( 0h -h A ) = ( -u 1 .h A ) )

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
    c0v
    c1
    cneg
    #
    cA
    csm
    co
    #
    cva
    co
    #
    @3
    c0v
    chil
    wcel
    @0
    @1
    @4
    wceq
    ax-hv0cl
    c0v
    cA
    hvsubval
    mpan
    @0
    @3
    chil
    wcel
    #
    @4
    @3
    wceq
    @2
    cc
    wcel
    @0
    @5
    neg1cn
    @2
    cA
    hvmulcl
    mpan
    @3
    hvaddid2
    syl
    eqtrd
end

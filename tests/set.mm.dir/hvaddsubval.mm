include "chil.mm"
include "wcel.mm"
include "wa.mm"
include "c1.mm"
include "cneg.mm"
include "csm.mm"
include "co.mm"
include "cmv.mm"
include "cva.mm"
include "wceq.mm"
include "cc.mm"
include "neg1cn.mm"
include "hvmulcl.mm"
include "mpan.mm"
include "hvsubval.mm"
include "sylan2.mm"
include "hvm1neg.mm"
include "negneg1e1.mm"
include "oveq1i.mm"
include "syl6eq.mm"
include "ax-hvmulid.mm"
include "eqtrd.mm"
include "adantl.mm"
include "oveq2d.mm"
include "eqtr2d.mm"

theorem hvaddsubval
  let cA: class A
  let cB: class B


  assert |- ( ( A e. ~H /\ B e. ~H ) -> ( A +h B ) = ( A -h ( -u 1 .h B ) ) )

  proof
    cA
    chil
    wcel
    #
    cB
    chil
    wcel
    #
    wa
    #
    cA
    c1
    cneg
    #
    cB
    csm
    co
    #
    cmv
    co
    #
    cA
    @3
    @4
    csm
    co
    #
    cva
    co
    #
    cA
    cB
    cva
    co
    @1
    @0
    @4
    chil
    wcel
    #
    @5
    @7
    wceq
    @3
    cc
    wcel
    #
    @1
    @8
    neg1cn
    @3
    cB
    hvmulcl
    mpan
    cA
    @4
    hvsubval
    sylan2
    @2
    @6
    cB
    cA
    cva
    @1
    @6
    cB
    wceq
    @0
    @1
    @6
    c1
    cB
    csm
    co
    #
    cB
    @1
    @6
    @3
    cneg
    #
    cB
    csm
    co
    #
    @10
    @9
    @1
    @6
    @12
    wceq
    neg1cn
    @3
    cB
    hvm1neg
    mpan
    @11
    c1
    cB
    csm
    negneg1e1
    oveq1i
    syl6eq
    cB
    ax-hvmulid
    eqtrd
    adantl
    oveq2d
    eqtr2d
end

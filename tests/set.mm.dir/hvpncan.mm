include "chil.mm"
include "wcel.mm"
include "wa.mm"
include "cva.mm"
include "co.mm"
include "cmv.mm"
include "c1.mm"
include "cneg.mm"
include "csm.mm"
include "wceq.mm"
include "hvaddcl.mm"
include "hvsubval.mm"
include "sylancom.mm"
include "cc.mm"
include "neg1cn.mm"
include "hvmulcl.mm"
include "mpan.mm"
include "ancli.mm"
include "ax-hvass.mm"
include "3expb.mm"
include "sylan2.mm"
include "c0v.mm"
include "hvnegid.mm"
include "oveq2d.mm"
include "ax-hvaddid.mm"
include "sylan9eqr.mm"
include "3eqtrd.mm"

theorem hvpncan
  let cA: class A
  let cB: class B


  assert |- ( ( A e. ~H /\ B e. ~H ) -> ( ( A +h B ) -h B ) = A )

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
    cA
    cB
    cva
    co
    #
    cB
    cmv
    co
    #
    @2
    c1
    cneg
    #
    cB
    csm
    co
    #
    cva
    co
    #
    cA
    cB
    @5
    cva
    co
    #
    cva
    co
    #
    cA
    @0
    @1
    @2
    chil
    wcel
    @3
    @6
    wceq
    cA
    cB
    hvaddcl
    @2
    cB
    hvsubval
    sylancom
    @1
    @0
    @1
    @5
    chil
    wcel
    #
    wa
    @6
    @8
    wceq
    #
    @1
    @9
    @4
    cc
    wcel
    @1
    @9
    neg1cn
    @4
    cB
    hvmulcl
    mpan
    ancli
    @0
    @1
    @9
    @10
    cA
    cB
    @5
    ax-hvass
    3expb
    sylan2
    @1
    @0
    @8
    cA
    c0v
    cva
    co
    cA
    @1
    @7
    c0v
    cA
    cva
    cB
    hvnegid
    oveq2d
    cA
    ax-hvaddid
    sylan9eqr
    3eqtrd
end

include "clo.mm"
include "wcel.mm"
include "cc.mm"
include "chil.mm"
include "w3a.mm"
include "csm.mm"
include "co.mm"
include "c0v.mm"
include "cva.mm"
include "cfv.mm"
include "wceq.mm"
include "wa.mm"
include "ax-hv0cl.mm"
include "lnopl.mm"
include "mpanr2.mm"
include "3impa.mm"
include "hvmulcl.mm"
include "ax-hvaddid.mm"
include "syl.mm"
include "3adant1.mm"
include "fveq2d.mm"
include "lnop0.mm"
include "oveq2d.mm"
include "3ad2ant1.mm"
include "lnopf.mm"
include "ffvelrnda.mm"
include "sylan2.mm"
include "3impb.mm"
include "3com12.mm"
include "eqtrd.mm"
include "3eqtr3d.mm"

theorem lnopmul
  let cA: class A
  let cB: class B
  let cT: class T


  assert |- ( ( T e. LinOp /\ A e. CC /\ B e. ~H ) -> ( T ` ( A .h B ) ) = ( A .h ( T ` B ) ) )

  proof
    cT
    clo
    wcel
    #
    cA
    cc
    wcel
    #
    cB
    chil
    wcel
    #
    w3a
    #
    cA
    cB
    csm
    co
    #
    c0v
    cva
    co
    #
    cT
    cfv
    #
    cA
    cB
    cT
    cfv
    #
    csm
    co
    #
    c0v
    cT
    cfv
    #
    cva
    co
    #
    @4
    cT
    cfv
    @8
    @0
    @1
    @2
    @6
    @10
    wceq
    #
    @0
    @1
    wa
    @2
    c0v
    chil
    wcel
    @11
    ax-hv0cl
    cA
    cB
    c0v
    cT
    lnopl
    mpanr2
    3impa
    @3
    @5
    @4
    cT
    @1
    @2
    @5
    @4
    wceq
    #
    @0
    @1
    @2
    wa
    @4
    chil
    wcel
    @12
    cA
    cB
    hvmulcl
    @4
    ax-hvaddid
    syl
    3adant1
    fveq2d
    @3
    @10
    @8
    c0v
    cva
    co
    #
    @8
    @0
    @1
    @10
    @13
    wceq
    @2
    @0
    @9
    c0v
    @8
    cva
    cT
    lnop0
    oveq2d
    3ad2ant1
    @3
    @8
    chil
    wcel
    #
    @13
    @8
    wceq
    @1
    @0
    @2
    @14
    @1
    @0
    @2
    @14
    @0
    @2
    wa
    @1
    @7
    chil
    wcel
    @14
    @0
    chil
    chil
    cB
    cT
    cT
    lnopf
    ffvelrnda
    cA
    @7
    hvmulcl
    sylan2
    3impb
    3com12
    @8
    ax-hvaddid
    syl
    eqtrd
    3eqtr3d
end

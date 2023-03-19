include "chil.mm"
include "wcel.mm"
include "wa.mm"
include "cva.mm"
include "co.mm"
include "c0v.mm"
include "wceq.mm"
include "c1.mm"
include "cneg.mm"
include "csm.mm"
include "cmv.mm"
include "hvaddsubval.mm"
include "eqeq1d.mm"
include "wb.mm"
include "cc.mm"
include "neg1cn.mm"
include "hvmulcl.mm"
include "mpan.mm"
include "hvsubeq0.mm"
include "sylan2.mm"
include "bitrd.mm"

theorem hvaddeq0
  let cA: class A
  let cB: class B


  assert |- ( ( A e. ~H /\ B e. ~H ) -> ( ( A +h B ) = 0h <-> A = ( -u 1 .h B ) ) )

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
    cB
    cva
    co
    #
    c0v
    wceq
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
    c0v
    wceq
    #
    cA
    @5
    wceq
    #
    @2
    @3
    @6
    c0v
    cA
    cB
    hvaddsubval
    eqeq1d
    @1
    @0
    @5
    chil
    wcel
    #
    @7
    @8
    wb
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
    cA
    @5
    hvsubeq0
    sylan2
    bitrd
end

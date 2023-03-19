include "cch.mm"
include "wcel.mm"
include "chil.mm"
include "wa.mm"
include "cort.mm"
include "cfv.mm"
include "cpjh.mm"
include "cmv.mm"
include "co.mm"
include "wceq.mm"
include "cva.mm"
include "choccl.mm"
include "pjhcl.mm"
include "sylan.mm"
include "ax-hvcom.mm"
include "syl2anc.mm"
include "axpjpj.mm"
include "eqtr4d.mm"
include "wb.mm"
include "simpr.mm"
include "hvsubadd.mm"
include "syl3anc.mm"
include "mpbird.mm"
include "eqcomd.mm"

theorem pjpo
  let cA: class A
  let cH: class H


  assert |- ( ( H e. CH /\ A e. ~H ) -> ( ( projh ` H ) ` A ) = ( A -h ( ( projh ` ( _|_ ` H ) ) ` A ) ) )

  proof
    cH
    cch
    wcel
    #
    cA
    chil
    wcel
    #
    wa
    #
    cA
    cA
    cH
    cort
    cfv
    #
    cpjh
    cfv
    cfv
    #
    cmv
    co
    #
    cA
    cH
    cpjh
    cfv
    cfv
    #
    @2
    @5
    @6
    wceq
    #
    @4
    @6
    cva
    co
    #
    cA
    wceq
    #
    @2
    @8
    @6
    @4
    cva
    co
    #
    cA
    @2
    @4
    chil
    wcel
    #
    @6
    chil
    wcel
    #
    @8
    @10
    wceq
    @0
    @3
    cch
    wcel
    @1
    @11
    cH
    choccl
    cA
    @3
    pjhcl
    sylan
    #
    cA
    cH
    pjhcl
    #
    @4
    @6
    ax-hvcom
    syl2anc
    cA
    cH
    axpjpj
    eqtr4d
    @2
    @1
    @11
    @12
    @7
    @9
    wb
    @0
    @1
    simpr
    @13
    @14
    cA
    @4
    @6
    hvsubadd
    syl3anc
    mpbird
    eqcomd
end

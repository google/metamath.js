include "cch.mm"
include "wcel.mm"
include "chil.mm"
include "wa.mm"
include "cpjh.mm"
include "cfv.mm"
include "cmv.mm"
include "co.mm"
include "cort.mm"
include "wceq.mm"
include "cva.mm"
include "axpjpj.mm"
include "eqcomd.mm"
include "wb.mm"
include "simpr.mm"
include "pjhcl.mm"
include "choccl.mm"
include "sylan.mm"
include "hvsubadd.mm"
include "syl3anc.mm"
include "mpbird.mm"

theorem pjop
  let cA: class A
  let cH: class H


  assert |- ( ( H e. CH /\ A e. ~H ) -> ( ( projh ` ( _|_ ` H ) ) ` A ) = ( A -h ( ( projh ` H ) ` A ) ) )

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
    cpjh
    cfv
    cfv
    #
    cmv
    co
    #
    cA
    cH
    cort
    cfv
    #
    cpjh
    cfv
    cfv
    #
    @2
    @4
    @6
    wceq
    #
    @3
    @6
    cva
    co
    #
    cA
    wceq
    #
    @2
    cA
    @8
    cA
    cH
    axpjpj
    eqcomd
    @2
    @1
    @3
    chil
    wcel
    @6
    chil
    wcel
    #
    @7
    @9
    wb
    @0
    @1
    simpr
    cA
    cH
    pjhcl
    @0
    @5
    cch
    wcel
    @1
    @10
    cH
    choccl
    cA
    @5
    pjhcl
    sylan
    cA
    @3
    @6
    hvsubadd
    syl3anc
    mpbird
    eqcomd
end

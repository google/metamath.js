include "cch.mm"
include "wcel.mm"
include "chil.mm"
include "wa.mm"
include "cort.mm"
include "cfv.mm"
include "cpjh.mm"
include "cmv.mm"
include "co.mm"
include "pjop.mm"
include "choccl.mm"
include "axpjcl.mm"
include "sylan.mm"
include "eqeltrrd.mm"

theorem pjoccl
  let cA: class A
  let cH: class H


  assert |- ( ( H e. CH /\ A e. ~H ) -> ( A -h ( ( projh ` H ) ` A ) ) e. ( _|_ ` H ) )

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
    cA
    cH
    cort
    cfv
    #
    cpjh
    cfv
    cfv
    #
    cA
    cA
    cH
    cpjh
    cfv
    cfv
    cmv
    co
    @2
    cA
    cH
    pjop
    @0
    @2
    cch
    wcel
    @1
    @3
    @2
    wcel
    cH
    choccl
    cA
    @2
    axpjcl
    sylan
    eqeltrrd
end

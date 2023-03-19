include "cee.mm"
include "cfv.mm"
include "wcel.mm"
include "wa.mm"
include "axsegconlem2.mm"
include "axsegconlem3.mm"
include "sqrtge0d.mm"

theorem axsegconlem5
  let cA: class A
  let cB: class B
  let cS: class S
  let cN: class N
  let vp: setvar p
  let cC: class C
  let cD: class D
  assume axsegconlem2.1: |- S = sum_ p e. ( 1 ... N ) ( ( ( A ` p ) - ( B ` p ) ) ^ 2 )

  disjoint A p
  disjoint B p
  disjoint N p
  disjoint C p
  disjoint D p
  assert |- ( ( A e. ( EE ` N ) /\ B e. ( EE ` N ) ) -> 0 <_ ( sqrt ` S ) )

  proof
    cA
    cN
    cee
    cfv
    #
    wcel
    cB
    @0
    wcel
    wa
    cS
    cA
    cB
    cS
    cN
    vp
    axsegconlem2.1
    axsegconlem2
    cA
    cB
    cS
    cN
    vp
    axsegconlem2.1
    axsegconlem3
    sqrtge0d
end

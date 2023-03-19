include "cuo.mm"
include "wcel.mm"
include "chil.mm"
include "w3a.mm"
include "cfv.mm"
include "ccnv.mm"
include "csp.mm"
include "co.mm"
include "wceq.mm"
include "wf1o.mm"
include "unopf1o.mm"
include "f1ocnvfv2.mm"
include "sylan.mm"
include "3adant2.mm"
include "oveq2d.mm"
include "wf.mm"
include "f1ocnv.mm"
include "f1of.mm"
include "3syl.mm"
include "ffvelrnda.mm"
include "unop.mm"
include "syld3an3.mm"
include "eqtr3d.mm"

theorem unopadj
  let cA: class A
  let cB: class B
  let cT: class T
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cC: class C
  let cS: class S


  assert |- ( ( T e. UniOp /\ A e. ~H /\ B e. ~H ) -> ( ( T ` A ) .ih B ) = ( A .ih ( `' T ` B ) ) )

  proof
    cT
    cuo
    wcel
    #
    cA
    chil
    wcel
    #
    cB
    chil
    wcel
    #
    w3a
    #
    cA
    cT
    cfv
    #
    cB
    cT
    ccnv
    #
    cfv
    #
    cT
    cfv
    #
    csp
    co
    #
    @4
    cB
    csp
    co
    cA
    @6
    csp
    co
    #
    @3
    @7
    cB
    @4
    csp
    @0
    @2
    @7
    cB
    wceq
    #
    @1
    @0
    chil
    chil
    cT
    wf1o
    #
    @2
    @10
    cT
    unopf1o
    #
    chil
    chil
    cB
    cT
    f1ocnvfv2
    sylan
    3adant2
    oveq2d
    @0
    @1
    @2
    @6
    chil
    wcel
    #
    @8
    @9
    wceq
    @0
    @2
    @13
    @1
    @0
    chil
    chil
    cB
    @5
    @0
    @11
    chil
    chil
    @5
    wf1o
    chil
    chil
    @5
    wf
    @12
    chil
    chil
    cT
    f1ocnv
    chil
    chil
    @5
    f1of
    3syl
    ffvelrnda
    3adant2
    cA
    @6
    cT
    unop
    syld3an3
    eqtr3d
end

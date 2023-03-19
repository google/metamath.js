include "cr.mm"
include "wcel.mm"
include "cz.mm"
include "caddc.mm"
include "co.mm"
include "cfl.mm"
include "cfv.mm"
include "wceq.mm"
include "wa.mm"
include "fladdz.mm"
include "cc.mm"
include "recn.mm"
include "zcn.mm"
include "addcom.mm"
include "syl2an.mm"
include "fveq2d.mm"
include "reflcl.mm"
include "recnd.mm"
include "3eqtr3d.mm"
include "ancoms.mm"

theorem flzadd
  let cA: class A
  let cN: class N


  assert |- ( ( N e. ZZ /\ A e. RR ) -> ( |_ ` ( N + A ) ) = ( N + ( |_ ` A ) ) )

  proof
    cA
    cr
    wcel
    #
    cN
    cz
    wcel
    #
    cN
    cA
    caddc
    co
    #
    cfl
    cfv
    #
    cN
    cA
    cfl
    cfv
    #
    caddc
    co
    #
    wceq
    @0
    @1
    wa
    #
    cA
    cN
    caddc
    co
    #
    cfl
    cfv
    @4
    cN
    caddc
    co
    #
    @3
    @5
    cA
    cN
    fladdz
    @6
    @7
    @2
    cfl
    @0
    cA
    cc
    wcel
    cN
    cc
    wcel
    #
    @7
    @2
    wceq
    @1
    cA
    recn
    cN
    zcn
    #
    cA
    cN
    addcom
    syl2an
    fveq2d
    @0
    @4
    cc
    wcel
    @9
    @8
    @5
    wceq
    @1
    @0
    @4
    cA
    reflcl
    recnd
    @10
    @4
    cN
    addcom
    syl2an
    3eqtr3d
    ancoms
end

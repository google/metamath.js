include "csh.mm"
include "wcel.mm"
include "wa.mm"
include "chj.mm"
include "co.mm"
include "cun.mm"
include "cort.mm"
include "cfv.mm"
include "shjval.mm"
include "wceq.mm"
include "ancoms.mm"
include "uncom.mm"
include "fveq2i.mm"
include "syl6eq.mm"
include "eqtr4d.mm"

theorem shjcom
  let cA: class A
  let cB: class B
  let vf: setvar f
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cC: class C
  let cD: class D


  assert |- ( ( A e. SH /\ B e. SH ) -> ( A vH B ) = ( B vH A ) )

  proof
    cA
    csh
    wcel
    #
    cB
    csh
    wcel
    #
    wa
    #
    cA
    cB
    chj
    co
    cA
    cB
    cun
    #
    cort
    cfv
    #
    cort
    cfv
    #
    cB
    cA
    chj
    co
    #
    cA
    cB
    shjval
    @2
    @6
    cB
    cA
    cun
    #
    cort
    cfv
    #
    cort
    cfv
    #
    @5
    @1
    @0
    @6
    @9
    wceq
    cB
    cA
    shjval
    ancoms
    @8
    @4
    cort
    @7
    @3
    cort
    cB
    cA
    uncom
    fveq2i
    fveq2i
    syl6eq
    eqtr4d
end

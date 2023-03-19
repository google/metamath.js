include "chil.mm"
include "wf.mm"
include "cc.mm"
include "wcel.mm"
include "cmap.mm"
include "co.mm"
include "chot.mm"
include "cv.mm"
include "cfv.mm"
include "csm.mm"
include "cmpt.mm"
include "wceq.mm"
include "ax-hilex.mm"
include "elmap.mm"
include "oveq1.mm"
include "mpteq2dv.mm"
include "fveq1.mm"
include "oveq2d.mm"
include "df-homul.mm"
include "mptex.mm"
include "ovmpt2.mm"
include "sylan2br.mm"

theorem hommval
  let vx: setvar x
  let cA: class A
  let cT: class T
  let vf: setvar f
  let vg: setvar g
  let cS: class S

  disjoint A x
  disjoint T x
  disjoint f g
  disjoint f x
  disjoint A f
  disjoint g x
  disjoint A g
  disjoint S f
  disjoint S g
  disjoint S x
  disjoint T f
  disjoint T g
  assert |- ( ( A e. CC /\ T : ~H --> ~H ) -> ( A .op T ) = ( x e. ~H |-> ( A .h ( T ` x ) ) ) )

  proof
    chil
    chil
    cT
    wf
    cA
    cc
    wcel
    cT
    chil
    chil
    cmap
    co
    #
    wcel
    cA
    cT
    chot
    co
    vx
    chil
    cA
    vx
    cv
    #
    cT
    cfv
    #
    csm
    co
    #
    cmpt
    #
    wceq
    chil
    chil
    cT
    ax-hilex
    ax-hilex
    elmap
    vf
    vg
    cA
    cT
    cc
    @0
    vx
    chil
    vf
    cv
    #
    @1
    vg
    cv
    #
    cfv
    #
    csm
    co
    #
    cmpt
    @4
    chot
    vx
    chil
    cA
    @7
    csm
    co
    #
    cmpt
    @5
    cA
    wceq
    vx
    chil
    @8
    @9
    @5
    cA
    @7
    csm
    oveq1
    mpteq2dv
    @6
    cT
    wceq
    #
    vx
    chil
    @9
    @3
    @10
    @7
    @2
    cA
    csm
    @1
    @6
    cT
    fveq1
    oveq2d
    mpteq2dv
    vx
    vf
    vg
    df-homul
    vx
    chil
    @3
    ax-hilex
    mptex
    ovmpt2
    sylan2br
end

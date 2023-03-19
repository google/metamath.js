include "chil.mm"
include "cc.mm"
include "wf.mm"
include "wcel.mm"
include "cmap.mm"
include "co.mm"
include "chft.mm"
include "cv.mm"
include "cfv.mm"
include "cmul.mm"
include "cmpt.mm"
include "wceq.mm"
include "cnex.mm"
include "ax-hilex.mm"
include "elmap.mm"
include "oveq1.mm"
include "mpteq2dv.mm"
include "fveq1.mm"
include "oveq2d.mm"
include "df-hfmul.mm"
include "mptex.mm"
include "ovmpt2.mm"
include "sylan2br.mm"

theorem hfmmval
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
  assert |- ( ( A e. CC /\ T : ~H --> CC ) -> ( A .fn T ) = ( x e. ~H |-> ( A x. ( T ` x ) ) ) )

  proof
    chil
    cc
    cT
    wf
    cA
    cc
    wcel
    cT
    cc
    chil
    cmap
    co
    #
    wcel
    cA
    cT
    chft
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
    cmul
    co
    #
    cmpt
    #
    wceq
    cc
    chil
    cT
    cnex
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
    cmul
    co
    #
    cmpt
    @4
    chft
    vx
    chil
    cA
    @7
    cmul
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
    cmul
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
    cmul
    @1
    @6
    cT
    fveq1
    oveq2d
    mpteq2dv
    vx
    vf
    vg
    df-hfmul
    vx
    chil
    @3
    ax-hilex
    mptex
    ovmpt2
    sylan2br
end

include "chil.mm"
include "wf.mm"
include "cmap.mm"
include "co.mm"
include "wcel.mm"
include "chos.mm"
include "cv.mm"
include "cfv.mm"
include "cva.mm"
include "cmpt.mm"
include "wceq.mm"
include "ax-hilex.mm"
include "elmap.mm"
include "fveq1.mm"
include "oveq1d.mm"
include "mpteq2dv.mm"
include "oveq2d.mm"
include "df-hosum.mm"
include "mptex.mm"
include "ovmpt2.mm"
include "syl2anbr.mm"

theorem hosmval
  let vx: setvar x
  let cS: class S
  let cT: class T
  let vf: setvar f
  let vg: setvar g
  let cA: class A

  disjoint S x
  disjoint T x
  disjoint f g
  disjoint f x
  disjoint A f
  disjoint g x
  disjoint A g
  disjoint A x
  disjoint S f
  disjoint S g
  disjoint T f
  disjoint T g
  assert |- ( ( S : ~H --> ~H /\ T : ~H --> ~H ) -> ( S +op T ) = ( x e. ~H |-> ( ( S ` x ) +h ( T ` x ) ) ) )

  proof
    chil
    chil
    cS
    wf
    cS
    chil
    chil
    cmap
    co
    #
    wcel
    cT
    @0
    wcel
    cS
    cT
    chos
    co
    vx
    chil
    vx
    cv
    #
    cS
    cfv
    #
    @1
    cT
    cfv
    #
    cva
    co
    #
    cmpt
    #
    wceq
    chil
    chil
    cT
    wf
    chil
    chil
    cS
    ax-hilex
    ax-hilex
    elmap
    chil
    chil
    cT
    ax-hilex
    ax-hilex
    elmap
    vf
    vg
    cS
    cT
    @0
    @0
    vx
    chil
    @1
    vf
    cv
    #
    cfv
    #
    @1
    vg
    cv
    #
    cfv
    #
    cva
    co
    #
    cmpt
    @5
    chos
    vx
    chil
    @2
    @9
    cva
    co
    #
    cmpt
    @6
    cS
    wceq
    #
    vx
    chil
    @10
    @11
    @12
    @7
    @2
    @9
    cva
    @1
    @6
    cS
    fveq1
    oveq1d
    mpteq2dv
    @8
    cT
    wceq
    #
    vx
    chil
    @11
    @4
    @13
    @9
    @3
    @2
    cva
    @1
    @8
    cT
    fveq1
    oveq2d
    mpteq2dv
    vx
    vf
    vg
    df-hosum
    vx
    chil
    @4
    ax-hilex
    mptex
    ovmpt2
    syl2anbr
end

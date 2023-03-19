include "chil.mm"
include "cc.mm"
include "wf.mm"
include "cmap.mm"
include "co.mm"
include "wcel.mm"
include "chfs.mm"
include "cv.mm"
include "cfv.mm"
include "caddc.mm"
include "cmpt.mm"
include "wceq.mm"
include "cnex.mm"
include "ax-hilex.mm"
include "elmap.mm"
include "fveq1.mm"
include "oveq1d.mm"
include "mpteq2dv.mm"
include "oveq2d.mm"
include "df-hfsum.mm"
include "mptex.mm"
include "ovmpt2.mm"
include "syl2anbr.mm"

theorem hfsmval
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
  assert |- ( ( S : ~H --> CC /\ T : ~H --> CC ) -> ( S +fn T ) = ( x e. ~H |-> ( ( S ` x ) + ( T ` x ) ) ) )

  proof
    chil
    cc
    cS
    wf
    cS
    cc
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
    chfs
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
    caddc
    co
    #
    cmpt
    #
    wceq
    chil
    cc
    cT
    wf
    cc
    chil
    cS
    cnex
    ax-hilex
    elmap
    cc
    chil
    cT
    cnex
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
    caddc
    co
    #
    cmpt
    @5
    chfs
    vx
    chil
    @2
    @9
    caddc
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
    caddc
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
    caddc
    @1
    @8
    cT
    fveq1
    oveq2d
    mpteq2dv
    vx
    vf
    vg
    df-hfsum
    vx
    chil
    @4
    ax-hilex
    mptex
    ovmpt2
    syl2anbr
end

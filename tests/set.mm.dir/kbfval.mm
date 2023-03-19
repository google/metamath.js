include "chil.mm"
include "cv.mm"
include "csp.mm"
include "co.mm"
include "csm.mm"
include "cmpt.mm"
include "ck.mm"
include "wceq.mm"
include "oveq2.mm"
include "mpteq2dv.mm"
include "oveq1d.mm"
include "df-kb.mm"
include "ax-hilex.mm"
include "mptex.mm"
include "ovmpt2.mm"

theorem kbfval
  let vx: setvar x
  let cA: class A
  let cB: class B
  let vw: setvar w
  let vy: setvar y
  let vz: setvar z
  let cC: class C
  let cS: class S
  let cT: class T

  disjoint A x
  disjoint B x
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint A w
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint B w
  disjoint B y
  disjoint B z
  disjoint C x
  disjoint C y
  disjoint C z
  disjoint S w
  disjoint S x
  disjoint S y
  disjoint S z
  disjoint T x
  disjoint T y
  disjoint T z
  disjoint T w
  assert |- ( ( A e. ~H /\ B e. ~H ) -> ( A ketbra B ) = ( x e. ~H |-> ( ( x .ih B ) .h A ) ) )

  proof
    vy
    vz
    cA
    cB
    chil
    chil
    vx
    chil
    vx
    cv
    #
    vz
    cv
    #
    csp
    co
    #
    vy
    cv
    #
    csm
    co
    #
    cmpt
    vx
    chil
    @0
    cB
    csp
    co
    #
    cA
    csm
    co
    #
    cmpt
    ck
    vx
    chil
    @2
    cA
    csm
    co
    #
    cmpt
    @3
    cA
    wceq
    vx
    chil
    @4
    @7
    @3
    cA
    @2
    csm
    oveq2
    mpteq2dv
    @1
    cB
    wceq
    #
    vx
    chil
    @7
    @6
    @8
    @2
    @5
    cA
    csm
    @1
    cB
    @0
    csp
    oveq2
    oveq1d
    mpteq2dv
    vy
    vz
    vx
    df-kb
    vx
    chil
    @6
    ax-hilex
    mptex
    ovmpt2
end

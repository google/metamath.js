include "chil.mm"
include "cv.mm"
include "csp.mm"
include "co.mm"
include "cmpt.mm"
include "cbr.mm"
include "wceq.mm"
include "oveq2.mm"
include "mpteq2dv.mm"
include "df-bra.mm"
include "ax-hilex.mm"
include "mptex.mm"
include "fvmpt.mm"

theorem brafval
  let vx: setvar x
  let cA: class A
  let vw: setvar w
  let vy: setvar y
  let vz: setvar z
  let cB: class B
  let cC: class C
  let cS: class S
  let cT: class T

  disjoint A x
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
  disjoint B x
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
  assert |- ( A e. ~H -> ( bra ` A ) = ( x e. ~H |-> ( x .ih A ) ) )

  proof
    vy
    cA
    vx
    chil
    vx
    cv
    #
    vy
    cv
    #
    csp
    co
    #
    cmpt
    vx
    chil
    @0
    cA
    csp
    co
    #
    cmpt
    chil
    cbr
    @1
    cA
    wceq
    vx
    chil
    @2
    @3
    @1
    cA
    @0
    csp
    oveq2
    mpteq2dv
    vy
    vx
    df-bra
    vx
    chil
    @3
    ax-hilex
    mptex
    fvmpt
end

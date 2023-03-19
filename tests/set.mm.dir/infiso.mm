include "cima.mm"
include "ccnv.mm"
include "csup.mm"
include "cfv.mm"
include "cinf.mm"
include "wiso.mm"
include "isocnv2.mm"
include "sylib.mm"
include "infcllem.mm"
include "wor.mm"
include "cnvso.mm"
include "supiso.mm"
include "df-inf.mm"
include "fveq2i.mm"
include "3eqtr4g.mm"

theorem infiso
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cC: class C
  let cR: class R
  let cS: class S
  let cF: class F
  assume infiso.1: |- ( ph -> F Isom R , S ( A , B ) )
  assume infiso.2: |- ( ph -> C C_ A )
  assume infiso.3: |- ( ph -> E. x e. A ( A. y e. C -. y R x /\ A. y e. A ( x R y -> E. z e. C z R y ) ) )
  assume infiso.4: |- ( ph -> R Or A )

  disjoint A x
  disjoint A y
  disjoint A z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint B x
  disjoint B y
  disjoint B z
  disjoint C x
  disjoint C y
  disjoint C z
  disjoint F x
  disjoint F y
  disjoint F z
  disjoint R x
  disjoint R y
  disjoint R z
  disjoint S x
  disjoint S y
  disjoint S z
  disjoint ph x
  disjoint ph y
  disjoint ph z
  assert |- ( ph -> inf ( ( F " C ) , B , S ) = ( F ` inf ( C , A , R ) ) )

  proof
    wph
    cF
    cC
    cima
    #
    cB
    cS
    ccnv
    #
    csup
    cC
    cA
    cR
    ccnv
    #
    csup
    #
    cF
    cfv
    @0
    cB
    cS
    cinf
    cC
    cA
    cR
    cinf
    #
    cF
    cfv
    wph
    vx
    vy
    vz
    cA
    cB
    cC
    @2
    @1
    cF
    wph
    cA
    cB
    cR
    cS
    cF
    wiso
    cA
    cB
    @2
    @1
    cF
    wiso
    infiso.1
    cA
    cB
    cR
    cS
    cF
    isocnv2
    sylib
    infiso.2
    wph
    vx
    vy
    vz
    cA
    cC
    cR
    infiso.4
    infiso.3
    infcllem
    wph
    cA
    cR
    wor
    cA
    @2
    wor
    infiso.4
    cA
    cR
    cnvso
    sylib
    supiso
    @0
    cB
    cS
    df-inf
    @4
    @3
    cF
    cC
    cA
    cR
    df-inf
    fveq2i
    3eqtr4g
end

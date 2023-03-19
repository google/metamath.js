include "cinf.mm"
include "ccnv.mm"
include "csup.mm"
include "df-inf.mm"
include "wor.mm"
include "cnvso.mm"
include "sylib.mm"
include "infcllem.mm"
include "supcl.mm"
include "syl5eqel.mm"

theorem infcl
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cR: class R
  assume infcl.1: |- ( ph -> R Or A )
  assume infcl.2: |- ( ph -> E. x e. A ( A. y e. B -. y R x /\ A. y e. A ( x R y -> E. z e. B z R y ) ) )

  disjoint A x
  disjoint A y
  disjoint A z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint B x
  disjoint B y
  disjoint B z
  disjoint R x
  disjoint R y
  disjoint R z
  assert |- ( ph -> inf ( B , A , R ) e. A )

  proof
    wph
    cB
    cA
    cR
    cinf
    cB
    cA
    cR
    ccnv
    #
    csup
    cA
    cB
    cA
    cR
    df-inf
    wph
    vx
    vy
    vz
    cA
    cB
    @0
    wph
    cA
    cR
    wor
    cA
    @0
    wor
    infcl.1
    cA
    cR
    cnvso
    sylib
    wph
    vx
    vy
    vz
    cA
    cB
    cR
    infcl.1
    infcl.2
    infcllem
    supcl
    syl5eqel
end

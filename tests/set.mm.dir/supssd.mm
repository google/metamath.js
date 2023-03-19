include "csup.mm"
include "wcel.mm"
include "cv.mm"
include "wbr.mm"
include "wn.mm"
include "wral.mm"
include "supcl.mm"
include "sseld.mm"
include "supub.mm"
include "syld.mm"
include "ralrimiv.mm"
include "supnub.mm"
include "mp2and.mm"

theorem supssd
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cC: class C
  let cR: class R
  assume supssd.0: |- ( ph -> R Or A )
  assume supssd.1: |- ( ph -> B C_ C )
  assume supssd.2: |- ( ph -> C C_ A )
  assume supssd.3: |- ( ph -> E. x e. A ( A. y e. B -. x R y /\ A. y e. A ( y R x -> E. z e. B y R z ) ) )
  assume supssd.4: |- ( ph -> E. x e. A ( A. y e. C -. x R y /\ A. y e. A ( y R x -> E. z e. C y R z ) ) )

  disjoint x y
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint B x
  disjoint B y
  disjoint B z
  disjoint C x
  disjoint C y
  disjoint C z
  disjoint R x
  disjoint R y
  disjoint R z
  disjoint ph z
  assert |- ( ph -> -. sup ( C , A , R ) R sup ( B , A , R ) )

  proof
    wph
    cC
    cA
    cR
    csup
    #
    cA
    wcel
    @0
    vz
    cv
    #
    cR
    wbr
    wn
    #
    vz
    cB
    wral
    @0
    cB
    cA
    cR
    csup
    cR
    wbr
    wn
    wph
    vx
    vy
    vz
    cA
    cC
    cR
    supssd.0
    supssd.4
    supcl
    wph
    @2
    vz
    cB
    wph
    @1
    cB
    wcel
    @1
    cC
    wcel
    @2
    wph
    cB
    cC
    @1
    supssd.1
    sseld
    wph
    vx
    vy
    vz
    cA
    cC
    @1
    cR
    supssd.0
    supssd.4
    supub
    syld
    ralrimiv
    wph
    vx
    vy
    vz
    cA
    cB
    @0
    cR
    supssd.0
    supssd.3
    supnub
    mp2and
end

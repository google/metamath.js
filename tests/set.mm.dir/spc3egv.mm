include "wcel.mm"
include "w3a.mm"
include "cv.mm"
include "wceq.mm"
include "wex.mm"
include "elisset.mm"
include "3anim123i.mm"
include "eeeanv.mm"
include "sylibr.mm"
include "biimprcd.mm"
include "eximdv.mm"
include "2eximdv.mm"
include "syl5com.mm"

theorem spc3egv
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cC: class C
  let cV: class V
  let cW: class W
  let cX: class X
  assume spc3egv.1: |- ( ( x = A /\ y = B /\ z = C ) -> ( ph <-> ps ) )

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
  disjoint ps x
  disjoint ps y
  disjoint ps z
  assert |- ( ( A e. V /\ B e. W /\ C e. X ) -> ( ps -> E. x E. y E. z ph ) )

  proof
    cA
    cV
    wcel
    #
    cB
    cW
    wcel
    #
    cC
    cX
    wcel
    #
    w3a
    #
    vx
    cv
    cA
    wceq
    #
    vy
    cv
    cB
    wceq
    #
    vz
    cv
    cC
    wceq
    #
    w3a
    #
    vz
    wex
    #
    vy
    wex
    vx
    wex
    #
    wps
    wph
    vz
    wex
    #
    vy
    wex
    vx
    wex
    @3
    @4
    vx
    wex
    #
    @5
    vy
    wex
    #
    @6
    vz
    wex
    #
    w3a
    @9
    @0
    @11
    @1
    @12
    @2
    @13
    vx
    cA
    cV
    elisset
    vy
    cB
    cW
    elisset
    vz
    cC
    cX
    elisset
    3anim123i
    @4
    @5
    @6
    vx
    vy
    vz
    eeeanv
    sylibr
    wps
    @8
    @10
    vx
    vy
    wps
    @7
    wph
    vz
    @7
    wph
    wps
    spc3egv.1
    biimprcd
    eximdv
    2eximdv
    syl5com
end

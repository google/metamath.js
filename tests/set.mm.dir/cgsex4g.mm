include "wcel.mm"
include "wa.mm"
include "wex.mm"
include "biimpa.mm"
include "exlimivv.mm"
include "cv.mm"
include "wceq.mm"
include "elisset.mm"
include "anim12i.mm"
include "eeanv.mm"
include "sylibr.mm"
include "ee4anv.mm"
include "2eximi.mm"
include "syl.mm"
include "biimprcd.mm"
include "ancld.mm"
include "2eximdv.mm"
include "syl5com.mm"
include "impbid2.mm"

theorem cgsex4g
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cR: class R
  let cS: class S
  assume cgsex4g.1: |- ( ( ( x = A /\ y = B ) /\ ( z = C /\ w = D ) ) -> ch )
  assume cgsex4g.2: |- ( ch -> ( ph <-> ps ) )

  disjoint x y
  disjoint x z
  disjoint w x
  disjoint A x
  disjoint y z
  disjoint w y
  disjoint A y
  disjoint w z
  disjoint A z
  disjoint A w
  disjoint B x
  disjoint B y
  disjoint B z
  disjoint B w
  disjoint C x
  disjoint C y
  disjoint C z
  disjoint C w
  disjoint D x
  disjoint D y
  disjoint D z
  disjoint D w
  disjoint ps x
  disjoint ps y
  disjoint ps z
  disjoint ps w
  assert |- ( ( ( A e. R /\ B e. S ) /\ ( C e. R /\ D e. S ) ) -> ( E. x E. y E. z E. w ( ch /\ ph ) <-> ps ) )

  proof
    cA
    cR
    wcel
    #
    cB
    cS
    wcel
    #
    wa
    #
    cC
    cR
    wcel
    #
    cD
    cS
    wcel
    #
    wa
    #
    wa
    #
    wch
    wph
    wa
    #
    vw
    wex
    vz
    wex
    #
    vy
    wex
    vx
    wex
    #
    wps
    @8
    wps
    vx
    vy
    @7
    wps
    vz
    vw
    wch
    wph
    wps
    cgsex4g.2
    biimpa
    exlimivv
    exlimivv
    @6
    wch
    vw
    wex
    vz
    wex
    #
    vy
    wex
    vx
    wex
    #
    wps
    @9
    @6
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
    wa
    #
    vz
    cv
    cC
    wceq
    #
    vw
    cv
    cD
    wceq
    #
    wa
    #
    wa
    #
    vw
    wex
    vz
    wex
    #
    vy
    wex
    vx
    wex
    #
    @11
    @6
    @14
    vy
    wex
    vx
    wex
    #
    @17
    vw
    wex
    vz
    wex
    #
    wa
    @20
    @2
    @21
    @5
    @22
    @2
    @12
    vx
    wex
    #
    @13
    vy
    wex
    #
    wa
    @21
    @0
    @23
    @1
    @24
    vx
    cA
    cR
    elisset
    vy
    cB
    cS
    elisset
    anim12i
    @12
    @13
    vx
    vy
    eeanv
    sylibr
    @5
    @15
    vz
    wex
    #
    @16
    vw
    wex
    #
    wa
    @22
    @3
    @25
    @4
    @26
    vz
    cC
    cR
    elisset
    vw
    cD
    cS
    elisset
    anim12i
    @15
    @16
    vz
    vw
    eeanv
    sylibr
    anim12i
    @14
    @17
    vx
    vy
    vz
    vw
    ee4anv
    sylibr
    @19
    @10
    vx
    vy
    @18
    wch
    vz
    vw
    cgsex4g.1
    2eximi
    2eximi
    syl
    wps
    @10
    @8
    vx
    vy
    wps
    wch
    @7
    vz
    vw
    wps
    wch
    wph
    wch
    wph
    wps
    cgsex4g.2
    biimprcd
    ancld
    2eximdv
    2eximdv
    syl5com
    impbid2
end

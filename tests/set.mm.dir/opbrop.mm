include "wcel.mm"
include "wa.mm"
include "cop.mm"
include "wbr.mm"
include "cxp.mm"
include "opelxpi.mm"
include "anim12i.mm"
include "cv.mm"
include "wceq.mm"
include "wex.mm"
include "opex.mm"
include "eleq1.mm"
include "anbi1d.mm"
include "eqeq1.mm"
include "4exbidv.mm"
include "anbi12d.mm"
include "anbi2d.mm"
include "brab.mm"
include "copsex4g.mm"
include "syl5bb.mm"
include "mpbirand.mm"

theorem opbrop
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let vv: setvar v
  let vu: setvar u
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cR: class R
  let cS: class S
  assume opbrop.1: |- ( ( ( z = A /\ w = B ) /\ ( v = C /\ u = D ) ) -> ( ph <-> ps ) )
  assume opbrop.2: |- R = { <. x , y >. | ( ( x e. ( S X. S ) /\ y e. ( S X. S ) ) /\ E. z E. w E. v E. u ( ( x = <. z , w >. /\ y = <. v , u >. ) /\ ph ) ) }

  disjoint x y
  disjoint x z
  disjoint w x
  disjoint v x
  disjoint u x
  disjoint A x
  disjoint y z
  disjoint w y
  disjoint v y
  disjoint u y
  disjoint A y
  disjoint w z
  disjoint v z
  disjoint u z
  disjoint A z
  disjoint v w
  disjoint u w
  disjoint A w
  disjoint u v
  disjoint A v
  disjoint A u
  disjoint B x
  disjoint B y
  disjoint B z
  disjoint B w
  disjoint B v
  disjoint B u
  disjoint C x
  disjoint C y
  disjoint C z
  disjoint C w
  disjoint C v
  disjoint C u
  disjoint D x
  disjoint D y
  disjoint D z
  disjoint D w
  disjoint D v
  disjoint D u
  disjoint S x
  disjoint S y
  disjoint S z
  disjoint S w
  disjoint S v
  disjoint S u
  disjoint ph x
  disjoint ph y
  disjoint ps z
  disjoint ps w
  disjoint ps v
  disjoint ps u
  assert |- ( ( ( A e. S /\ B e. S ) /\ ( C e. S /\ D e. S ) ) -> ( <. A , B >. R <. C , D >. <-> ps ) )

  proof
    cA
    cS
    wcel
    cB
    cS
    wcel
    wa
    #
    cC
    cS
    wcel
    cD
    cS
    wcel
    wa
    #
    wa
    #
    cA
    cB
    cop
    #
    cC
    cD
    cop
    #
    cR
    wbr
    #
    @3
    cS
    cS
    cxp
    #
    wcel
    #
    @4
    @6
    wcel
    #
    wa
    #
    wps
    @0
    @7
    @1
    @8
    cA
    cB
    cS
    cS
    opelxpi
    cC
    cD
    cS
    cS
    opelxpi
    anim12i
    @5
    @9
    @3
    vz
    cv
    vw
    cv
    cop
    #
    wceq
    #
    @4
    vv
    cv
    vu
    cv
    cop
    #
    wceq
    #
    wa
    #
    wph
    wa
    #
    vu
    wex
    vv
    wex
    vw
    wex
    vz
    wex
    #
    wa
    #
    @2
    @9
    wps
    wa
    vx
    cv
    #
    @6
    wcel
    #
    vy
    cv
    #
    @6
    wcel
    #
    wa
    #
    @18
    @10
    wceq
    #
    @20
    @12
    wceq
    #
    wa
    #
    wph
    wa
    #
    vu
    wex
    vv
    wex
    vw
    wex
    vz
    wex
    #
    wa
    @7
    @21
    wa
    #
    @11
    @24
    wa
    #
    wph
    wa
    #
    vu
    wex
    vv
    wex
    vw
    wex
    vz
    wex
    #
    wa
    @17
    vx
    vy
    @3
    @4
    cR
    cA
    cB
    opex
    cC
    cD
    opex
    @18
    @3
    wceq
    #
    @22
    @28
    @27
    @31
    @32
    @19
    @7
    @21
    @18
    @3
    @6
    eleq1
    anbi1d
    @32
    @26
    @30
    vz
    vw
    vv
    vu
    @32
    @25
    @29
    wph
    @32
    @23
    @11
    @24
    @18
    @3
    @10
    eqeq1
    anbi1d
    anbi1d
    4exbidv
    anbi12d
    @20
    @4
    wceq
    #
    @28
    @9
    @31
    @16
    @33
    @21
    @8
    @7
    @20
    @4
    @6
    eleq1
    anbi2d
    @33
    @30
    @15
    vz
    vw
    vv
    vu
    @33
    @29
    @14
    wph
    @33
    @24
    @13
    @11
    @20
    @4
    @12
    eqeq1
    anbi2d
    anbi1d
    4exbidv
    anbi12d
    opbrop.2
    brab
    @2
    @16
    wps
    @9
    wph
    wps
    vz
    vw
    vv
    vu
    cA
    cB
    cC
    cD
    cS
    cS
    opbrop.1
    copsex4g
    anbi2d
    syl5bb
    mpbirand
end

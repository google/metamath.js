include "wcel.mm"
include "cv.mm"
include "wceq.mm"
include "wa.mm"
include "wex.mm"
include "wsbc.mm"
include "wb.mm"
include "weq.mm"
include "eqeq2.mm"
include "anbi2d.mm"
include "anbi1d.mm"
include "2exbidv.mm"
include "dfsbcq.mm"
include "sbcbidv.mm"
include "bibi12d.mm"
include "sbc5.mm"
include "19.42v.mm"
include "anass.mm"
include "exbii.mm"
include "anbi2i.mm"
include "3bitr4ri.mm"
include "bitr2i.mm"
include "vtocl2g.mm"
include "ancoms.mm"

theorem 2sbc5g
  let wph: wff ph
  let vz: setvar z
  let vw: setvar w
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let vx: setvar x
  let vy: setvar y

  disjoint w z
  disjoint A w
  disjoint A z
  disjoint B w
  disjoint B z
  disjoint w x
  disjoint w y
  disjoint x y
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint B x
  disjoint B y
  disjoint ph x
  disjoint ph y
  assert |- ( ( A e. C /\ B e. D ) -> ( E. z E. w ( ( z = A /\ w = B ) /\ ph ) <-> [. A / z ]. [. B / w ]. ph ) )

  proof
    cB
    cD
    wcel
    cA
    cC
    wcel
    vz
    cv
    #
    cA
    wceq
    #
    vw
    cv
    #
    cB
    wceq
    #
    wa
    #
    wph
    wa
    #
    vw
    wex
    vz
    wex
    #
    wph
    vw
    cB
    wsbc
    #
    vz
    cA
    wsbc
    #
    wb
    #
    vz
    vx
    weq
    #
    vw
    vy
    weq
    #
    wa
    #
    wph
    wa
    #
    vw
    wex
    #
    vz
    wex
    #
    wph
    vw
    vy
    cv
    #
    wsbc
    #
    vz
    vx
    cv
    #
    wsbc
    #
    wb
    @10
    @3
    wa
    #
    wph
    wa
    #
    vw
    wex
    vz
    wex
    #
    @7
    vz
    @18
    wsbc
    #
    wb
    @9
    vy
    vx
    cB
    cA
    cD
    cC
    @16
    cB
    wceq
    #
    @15
    @22
    @19
    @23
    @24
    @13
    @21
    vz
    vw
    @24
    @12
    @20
    wph
    @24
    @11
    @3
    @10
    @16
    cB
    @2
    eqeq2
    anbi2d
    anbi1d
    2exbidv
    @24
    @17
    @7
    vz
    @18
    wph
    vw
    @16
    cB
    dfsbcq
    sbcbidv
    bibi12d
    @18
    cA
    wceq
    #
    @22
    @6
    @23
    @8
    @25
    @21
    @5
    vz
    vw
    @25
    @20
    @4
    wph
    @25
    @10
    @1
    @3
    @18
    cA
    @0
    eqeq2
    anbi1d
    anbi1d
    2exbidv
    @7
    vz
    @18
    cA
    dfsbcq
    bibi12d
    @19
    @10
    @17
    wa
    #
    vz
    wex
    @15
    @17
    vz
    @18
    sbc5
    @26
    @14
    vz
    @10
    @11
    wph
    wa
    #
    wa
    #
    vw
    wex
    @10
    @27
    vw
    wex
    #
    wa
    @14
    @26
    @10
    @27
    vw
    19.42v
    @13
    @28
    vw
    @10
    @11
    wph
    anass
    exbii
    @17
    @29
    @10
    wph
    vw
    @16
    sbc5
    anbi2i
    3bitr4ri
    exbii
    bitr2i
    vtocl2g
    ancoms
end

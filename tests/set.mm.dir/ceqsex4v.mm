include "cv.mm"
include "wceq.mm"
include "wa.mm"
include "w3a.mm"
include "wex.mm"
include "19.42vv.mm"
include "3anass.mm"
include "df-3an.mm"
include "anbi2i.mm"
include "bitr4i.mm"
include "2exbii.mm"
include "3bitr4i.mm"
include "3anbi3d.mm"
include "2exbidv.mm"
include "ceqsex2v.mm"
include "3bitri.mm"

theorem ceqsex4v
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  assume ceqsex4v.1: |- A e. _V
  assume ceqsex4v.2: |- B e. _V
  assume ceqsex4v.3: |- C e. _V
  assume ceqsex4v.4: |- D e. _V
  assume ceqsex4v.7: |- ( x = A -> ( ph <-> ps ) )
  assume ceqsex4v.8: |- ( y = B -> ( ps <-> ch ) )
  assume ceqsex4v.9: |- ( z = C -> ( ch <-> th ) )
  assume ceqsex4v.10: |- ( w = D -> ( th <-> ta ) )

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
  disjoint ch y
  disjoint th z
  disjoint ta w
  assert |- ( E. x E. y E. z E. w ( ( x = A /\ y = B ) /\ ( z = C /\ w = D ) /\ ph ) <-> ta )

  proof
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
    wph
    w3a
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
    @0
    @1
    @3
    @4
    wph
    w3a
    #
    vw
    wex
    vz
    wex
    #
    w3a
    #
    vy
    wex
    vx
    wex
    @3
    @4
    wch
    w3a
    #
    vw
    wex
    vz
    wex
    #
    wta
    @7
    @10
    vx
    vy
    @2
    @8
    wa
    #
    vw
    wex
    vz
    wex
    @2
    @9
    wa
    @7
    @10
    @2
    @8
    vz
    vw
    19.42vv
    @6
    @13
    vz
    vw
    @6
    @2
    @5
    wph
    wa
    #
    wa
    @13
    @2
    @5
    wph
    3anass
    @8
    @14
    @2
    @3
    @4
    wph
    df-3an
    anbi2i
    bitr4i
    2exbii
    @0
    @1
    @9
    df-3an
    3bitr4i
    2exbii
    @9
    @3
    @4
    wps
    w3a
    #
    vw
    wex
    vz
    wex
    @12
    vx
    vy
    cA
    cB
    ceqsex4v.1
    ceqsex4v.2
    @0
    @8
    @15
    vz
    vw
    @0
    wph
    wps
    @3
    @4
    ceqsex4v.7
    3anbi3d
    2exbidv
    @1
    @15
    @11
    vz
    vw
    @1
    wps
    wch
    @3
    @4
    ceqsex4v.8
    3anbi3d
    2exbidv
    ceqsex2v
    wch
    wth
    wta
    vz
    vw
    cC
    cD
    ceqsex4v.3
    ceqsex4v.4
    ceqsex4v.9
    ceqsex4v.10
    ceqsex2v
    3bitri
end

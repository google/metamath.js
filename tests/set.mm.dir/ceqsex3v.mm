include "cv.mm"
include "wceq.mm"
include "w3a.mm"
include "wa.mm"
include "wex.mm"
include "anass.mm"
include "3anass.mm"
include "anbi1i.mm"
include "df-3an.mm"
include "anbi2i.mm"
include "3bitr4i.mm"
include "2exbii.mm"
include "19.42vv.mm"
include "bitri.mm"
include "exbii.mm"
include "3anbi3d.mm"
include "2exbidv.mm"
include "ceqsexv.mm"
include "ceqsex2v.mm"

theorem ceqsex3v
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cC: class C
  assume ceqsex3v.1: |- A e. _V
  assume ceqsex3v.2: |- B e. _V
  assume ceqsex3v.3: |- C e. _V
  assume ceqsex3v.4: |- ( x = A -> ( ph <-> ps ) )
  assume ceqsex3v.5: |- ( y = B -> ( ps <-> ch ) )
  assume ceqsex3v.6: |- ( z = C -> ( ch <-> th ) )

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
  disjoint ch y
  disjoint th z
  assert |- ( E. x E. y E. z ( ( x = A /\ y = B /\ z = C ) /\ ph ) <-> th )

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
    vz
    cv
    cC
    wceq
    #
    w3a
    #
    wph
    wa
    #
    vz
    wex
    vy
    wex
    #
    vx
    wex
    @0
    @1
    @2
    wph
    w3a
    #
    vz
    wex
    vy
    wex
    #
    wa
    #
    vx
    wex
    #
    wth
    @5
    @8
    vx
    @5
    @0
    @6
    wa
    #
    vz
    wex
    vy
    wex
    @8
    @4
    @10
    vy
    vz
    @0
    @1
    @2
    wa
    #
    wa
    #
    wph
    wa
    @0
    @11
    wph
    wa
    #
    wa
    @4
    @10
    @0
    @11
    wph
    anass
    @3
    @12
    wph
    @0
    @1
    @2
    3anass
    anbi1i
    @6
    @13
    @0
    @1
    @2
    wph
    df-3an
    anbi2i
    3bitr4i
    2exbii
    @0
    @6
    vy
    vz
    19.42vv
    bitri
    exbii
    @9
    @1
    @2
    wps
    w3a
    #
    vz
    wex
    vy
    wex
    #
    wth
    @7
    @15
    vx
    cA
    ceqsex3v.1
    @0
    @6
    @14
    vy
    vz
    @0
    wph
    wps
    @1
    @2
    ceqsex3v.4
    3anbi3d
    2exbidv
    ceqsexv
    wps
    wch
    wth
    vy
    vz
    cB
    cC
    ceqsex3v.2
    ceqsex3v.3
    ceqsex3v.5
    ceqsex3v.6
    ceqsex2v
    bitri
    bitri
end

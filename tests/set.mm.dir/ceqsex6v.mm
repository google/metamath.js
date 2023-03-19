include "cv.mm"
include "wceq.mm"
include "w3a.mm"
include "wex.mm"
include "wa.mm"
include "3anass.mm"
include "3exbii.mm"
include "19.42vvv.mm"
include "bitri.mm"
include "anbi2d.mm"
include "3exbidv.mm"
include "ceqsex3v.mm"

theorem ceqsex6v
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  let wze: wff ze
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
  let cE: class E
  let cF: class F
  assume ceqsex6v.1: |- A e. _V
  assume ceqsex6v.2: |- B e. _V
  assume ceqsex6v.3: |- C e. _V
  assume ceqsex6v.4: |- D e. _V
  assume ceqsex6v.5: |- E e. _V
  assume ceqsex6v.6: |- F e. _V
  assume ceqsex6v.7: |- ( x = A -> ( ph <-> ps ) )
  assume ceqsex6v.8: |- ( y = B -> ( ps <-> ch ) )
  assume ceqsex6v.9: |- ( z = C -> ( ch <-> th ) )
  assume ceqsex6v.10: |- ( w = D -> ( th <-> ta ) )
  assume ceqsex6v.11: |- ( v = E -> ( ta <-> et ) )
  assume ceqsex6v.12: |- ( u = F -> ( et <-> ze ) )

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
  disjoint E x
  disjoint E y
  disjoint E z
  disjoint E w
  disjoint E v
  disjoint E u
  disjoint F x
  disjoint F y
  disjoint F z
  disjoint F w
  disjoint F v
  disjoint F u
  disjoint ps x
  disjoint ch y
  disjoint th z
  disjoint ta w
  disjoint et v
  disjoint u ze
  assert |- ( E. x E. y E. z E. w E. v E. u ( ( x = A /\ y = B /\ z = C ) /\ ( w = D /\ v = E /\ u = F ) /\ ph ) <-> ze )

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
    vw
    cv
    cD
    wceq
    vv
    cv
    cE
    wceq
    vu
    cv
    cF
    wceq
    w3a
    #
    wph
    w3a
    #
    vu
    wex
    vv
    wex
    vw
    wex
    #
    vz
    wex
    vy
    wex
    vx
    wex
    @3
    @4
    wph
    wa
    #
    vu
    wex
    vv
    wex
    vw
    wex
    #
    wa
    #
    vz
    wex
    vy
    wex
    vx
    wex
    #
    wze
    @6
    @9
    vx
    vy
    vz
    @6
    @3
    @7
    wa
    #
    vu
    wex
    vv
    wex
    vw
    wex
    @9
    @5
    @11
    vw
    vv
    vu
    @3
    @4
    wph
    3anass
    3exbii
    @3
    @7
    vw
    vv
    vu
    19.42vvv
    bitri
    3exbii
    @10
    @4
    wth
    wa
    #
    vu
    wex
    vv
    wex
    vw
    wex
    #
    wze
    @8
    @4
    wps
    wa
    #
    vu
    wex
    vv
    wex
    vw
    wex
    @4
    wch
    wa
    #
    vu
    wex
    vv
    wex
    vw
    wex
    @13
    vx
    vy
    vz
    cA
    cB
    cC
    ceqsex6v.1
    ceqsex6v.2
    ceqsex6v.3
    @0
    @7
    @14
    vw
    vv
    vu
    @0
    wph
    wps
    @4
    ceqsex6v.7
    anbi2d
    3exbidv
    @1
    @14
    @15
    vw
    vv
    vu
    @1
    wps
    wch
    @4
    ceqsex6v.8
    anbi2d
    3exbidv
    @2
    @15
    @12
    vw
    vv
    vu
    @2
    wch
    wth
    @4
    ceqsex6v.9
    anbi2d
    3exbidv
    ceqsex3v
    wth
    wta
    wet
    wze
    vw
    vv
    vu
    cD
    cE
    cF
    ceqsex6v.4
    ceqsex6v.5
    ceqsex6v.6
    ceqsex6v.10
    ceqsex6v.11
    ceqsex6v.12
    ceqsex3v
    bitri
    bitri
end

include "cv.mm"
include "wceq.mm"
include "wa.mm"
include "w3a.mm"
include "wex.mm"
include "19.42vv.mm"
include "2exbii.mm"
include "bitri.mm"
include "3anass.mm"
include "df-3an.mm"
include "anbi2i.mm"
include "bitr4i.mm"
include "3bitr4i.mm"
include "3anbi3d.mm"
include "4exbidv.mm"
include "ceqsex4v.mm"

theorem ceqsex8v
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  let wze: wff ze
  let wsi: wff si
  let wrh: wff rh
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let vv: setvar v
  let vu: setvar u
  let vt: setvar t
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cE: class E
  let cF: class F
  let cG: class G
  let cH: class H
  let vs: setvar s
  assume ceqsex8v.1: |- A e. _V
  assume ceqsex8v.2: |- B e. _V
  assume ceqsex8v.3: |- C e. _V
  assume ceqsex8v.4: |- D e. _V
  assume ceqsex8v.5: |- E e. _V
  assume ceqsex8v.6: |- F e. _V
  assume ceqsex8v.7: |- G e. _V
  assume ceqsex8v.8: |- H e. _V
  assume ceqsex8v.9: |- ( x = A -> ( ph <-> ps ) )
  assume ceqsex8v.10: |- ( y = B -> ( ps <-> ch ) )
  assume ceqsex8v.11: |- ( z = C -> ( ch <-> th ) )
  assume ceqsex8v.12: |- ( w = D -> ( th <-> ta ) )
  assume ceqsex8v.13: |- ( v = E -> ( ta <-> et ) )
  assume ceqsex8v.14: |- ( u = F -> ( et <-> ze ) )
  assume ceqsex8v.15: |- ( t = G -> ( ze <-> si ) )
  assume ceqsex8v.16: |- ( s = H -> ( si <-> rh ) )

  disjoint x y
  disjoint x z
  disjoint w x
  disjoint v x
  disjoint u x
  disjoint t x
  disjoint s x
  disjoint A x
  disjoint y z
  disjoint w y
  disjoint v y
  disjoint u y
  disjoint t y
  disjoint s y
  disjoint A y
  disjoint w z
  disjoint v z
  disjoint u z
  disjoint t z
  disjoint s z
  disjoint A z
  disjoint v w
  disjoint u w
  disjoint t w
  disjoint s w
  disjoint A w
  disjoint u v
  disjoint t v
  disjoint s v
  disjoint A v
  disjoint t u
  disjoint s u
  disjoint A u
  disjoint s t
  disjoint A t
  disjoint A s
  disjoint B x
  disjoint B y
  disjoint B z
  disjoint B w
  disjoint B v
  disjoint B u
  disjoint B t
  disjoint B s
  disjoint C x
  disjoint C y
  disjoint C z
  disjoint C w
  disjoint C v
  disjoint C u
  disjoint C t
  disjoint C s
  disjoint D x
  disjoint D y
  disjoint D z
  disjoint D w
  disjoint D v
  disjoint D u
  disjoint D t
  disjoint D s
  disjoint E x
  disjoint E y
  disjoint E z
  disjoint E w
  disjoint E v
  disjoint E u
  disjoint E t
  disjoint E s
  disjoint F x
  disjoint F y
  disjoint F z
  disjoint F w
  disjoint F v
  disjoint F u
  disjoint F t
  disjoint F s
  disjoint G x
  disjoint G y
  disjoint G z
  disjoint G w
  disjoint G v
  disjoint G u
  disjoint G t
  disjoint G s
  disjoint H x
  disjoint H y
  disjoint H z
  disjoint H w
  disjoint H v
  disjoint H u
  disjoint H t
  disjoint H s
  disjoint ps x
  disjoint ch y
  disjoint th z
  disjoint ta w
  disjoint et v
  disjoint u ze
  disjoint si t
  disjoint rh s
  assert |- ( E. x E. y E. z E. w E. v E. u E. t E. s ( ( ( x = A /\ y = B ) /\ ( z = C /\ w = D ) ) /\ ( ( v = E /\ u = F ) /\ ( t = G /\ s = H ) ) /\ ph ) <-> rh )

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
    wa
    #
    vv
    cv
    cE
    wceq
    vu
    cv
    cF
    wceq
    wa
    #
    vt
    cv
    cG
    wceq
    vs
    cv
    cH
    wceq
    wa
    #
    wa
    #
    wph
    w3a
    #
    vs
    wex
    vt
    wex
    #
    vu
    wex
    vv
    wex
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
    @2
    @5
    @7
    @8
    wph
    w3a
    #
    vs
    wex
    vt
    wex
    #
    vu
    wex
    vv
    wex
    #
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
    #
    wrh
    @13
    @18
    vx
    vy
    @12
    @17
    vz
    vw
    @6
    @14
    wa
    #
    vs
    wex
    vt
    wex
    #
    vu
    wex
    vv
    wex
    #
    @6
    @16
    wa
    #
    @12
    @17
    @22
    @6
    @15
    wa
    #
    vu
    wex
    vv
    wex
    @23
    @21
    @24
    vv
    vu
    @6
    @14
    vt
    vs
    19.42vv
    2exbii
    @6
    @15
    vv
    vu
    19.42vv
    bitri
    @11
    @21
    vv
    vu
    @10
    @20
    vt
    vs
    @10
    @6
    @9
    wph
    wa
    #
    wa
    @20
    @6
    @9
    wph
    3anass
    @14
    @25
    @6
    @7
    @8
    wph
    df-3an
    anbi2i
    bitr4i
    2exbii
    2exbii
    @2
    @5
    @16
    df-3an
    3bitr4i
    2exbii
    2exbii
    @19
    @7
    @8
    wta
    w3a
    #
    vs
    wex
    vt
    wex
    vu
    wex
    vv
    wex
    #
    wrh
    @16
    @7
    @8
    wps
    w3a
    #
    vs
    wex
    vt
    wex
    vu
    wex
    vv
    wex
    @7
    @8
    wch
    w3a
    #
    vs
    wex
    vt
    wex
    vu
    wex
    vv
    wex
    @7
    @8
    wth
    w3a
    #
    vs
    wex
    vt
    wex
    vu
    wex
    vv
    wex
    @27
    vx
    vy
    vz
    vw
    cA
    cB
    cC
    cD
    ceqsex8v.1
    ceqsex8v.2
    ceqsex8v.3
    ceqsex8v.4
    @0
    @14
    @28
    vv
    vu
    vt
    vs
    @0
    wph
    wps
    @7
    @8
    ceqsex8v.9
    3anbi3d
    4exbidv
    @1
    @28
    @29
    vv
    vu
    vt
    vs
    @1
    wps
    wch
    @7
    @8
    ceqsex8v.10
    3anbi3d
    4exbidv
    @3
    @29
    @30
    vv
    vu
    vt
    vs
    @3
    wch
    wth
    @7
    @8
    ceqsex8v.11
    3anbi3d
    4exbidv
    @4
    @30
    @26
    vv
    vu
    vt
    vs
    @4
    wth
    wta
    @7
    @8
    ceqsex8v.12
    3anbi3d
    4exbidv
    ceqsex4v
    wta
    wet
    wze
    wsi
    wrh
    vv
    vu
    vt
    vs
    cE
    cF
    cG
    cH
    ceqsex8v.5
    ceqsex8v.6
    ceqsex8v.7
    ceqsex8v.8
    ceqsex8v.13
    ceqsex8v.14
    ceqsex8v.15
    ceqsex8v.16
    ceqsex4v
    bitri
    bitri
end

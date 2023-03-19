include "cv.mm"
include "c-bnj18.mm"
include "wcel.mm"
include "biid.mm"
include "bnj1033.mm"

theorem bnj1034
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wze: wff ze
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cD: class D
  let cR: class R
  let vf: setvar f
  let vi: setvar i
  let vn: setvar n
  let cK: class K
  let cX: class X
  assume bnj1034.1: |- ( ph <-> ( f ` (/) ) = _pred ( X , A , R ) )
  assume bnj1034.2: |- ( ps <-> A. i e. _om ( suc i e. n -> ( f ` suc i ) = U_ y e. ( f ` i ) _pred ( y , A , R ) ) )
  assume bnj1034.3: |- ( ch <-> ( n e. D /\ f Fn n /\ ph /\ ps ) )
  assume bnj1034.4: |- ( th <-> ( R _FrSe A /\ X e. A ) )
  assume bnj1034.5: |- ( ta <-> ( B e. _V /\ _TrFo ( B , A , R ) /\ _pred ( X , A , R ) C_ B ) )
  assume bnj1034.7: |- ( ze <-> ( i e. n /\ z e. ( f ` i ) ) )
  assume bnj1034.8: |- D = ( _om \ { (/) } )
  assume bnj1034.9: |- K = { f | E. n e. D ( f Fn n /\ ph /\ ps ) }
  assume bnj1034.10: |- ( E. f E. n E. i ( th /\ ta /\ ch /\ ze ) -> z e. B )

  disjoint A f
  disjoint A i
  disjoint A n
  disjoint A y
  disjoint f i
  disjoint f n
  disjoint f y
  disjoint i n
  disjoint i y
  disjoint n y
  disjoint A z
  disjoint f z
  disjoint i z
  disjoint n z
  disjoint B z
  disjoint D i
  disjoint R f
  disjoint R i
  disjoint R n
  disjoint R y
  disjoint R z
  disjoint X f
  disjoint X i
  disjoint X n
  disjoint X y
  disjoint X z
  disjoint f ta
  disjoint i ta
  disjoint n ta
  disjoint ta z
  disjoint f th
  disjoint i th
  disjoint n th
  disjoint th z
  disjoint i ph
  assert |- ( ( th /\ ta ) -> _trCl ( X , A , R ) C_ B )

  proof
    wph
    wps
    wch
    wth
    wta
    vz
    cv
    cA
    cR
    cX
    c-bnj18
    wcel
    #
    wze
    vy
    vz
    cA
    cB
    cD
    cR
    vf
    vi
    vn
    cK
    cX
    bnj1034.1
    bnj1034.2
    bnj1034.3
    bnj1034.4
    bnj1034.5
    @0
    biid
    bnj1034.7
    bnj1034.8
    bnj1034.9
    bnj1034.10
    bnj1033
end

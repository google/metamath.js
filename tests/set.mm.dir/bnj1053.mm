include "w-bnj17.mm"
include "cv.mm"
include "cep.mm"
include "wfr.mm"
include "wi.mm"
include "wral.mm"
include "wcel.mm"
include "wfn.mm"
include "com.mm"
include "word.mm"
include "bnj923.mm"
include "nnord.mm"
include "ordfr.mm"
include "3syl.mm"
include "bnj769.mm"
include "bnj707.mm"
include "jca.mm"
include "bnj1052.mm"

theorem bnj1053
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  let wze: wff ze
  let wrh: wff rh
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cD: class D
  let cR: class R
  let vf: setvar f
  let vi: setvar i
  let vj: setvar j
  let vn: setvar n
  let cK: class K
  let cX: class X
  assume bnj1053.1: |- ( ph <-> ( f ` (/) ) = _pred ( X , A , R ) )
  assume bnj1053.2: |- ( ps <-> A. i e. _om ( suc i e. n -> ( f ` suc i ) = U_ y e. ( f ` i ) _pred ( y , A , R ) ) )
  assume bnj1053.3: |- ( ch <-> ( n e. D /\ f Fn n /\ ph /\ ps ) )
  assume bnj1053.4: |- ( th <-> ( R _FrSe A /\ X e. A ) )
  assume bnj1053.5: |- ( ta <-> ( B e. _V /\ _TrFo ( B , A , R ) /\ _pred ( X , A , R ) C_ B ) )
  assume bnj1053.6: |- ( ze <-> ( i e. n /\ z e. ( f ` i ) ) )
  assume bnj1053.7: |- D = ( _om \ { (/) } )
  assume bnj1053.8: |- K = { f | E. n e. D ( f Fn n /\ ph /\ ps ) }
  assume bnj1053.9: |- ( et <-> ( ( th /\ ta /\ ch /\ ze ) -> z e. B ) )
  assume bnj1053.10: |- ( rh <-> A. j e. n ( j _E i -> [. j / i ]. et ) )
  assume bnj1053.37: |- ( ( th /\ ta /\ ch /\ ze ) -> A. i e. n ( rh -> et ) )

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
  disjoint B f
  disjoint B i
  disjoint B n
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
  disjoint et j
  disjoint f ta
  disjoint i ta
  disjoint n ta
  disjoint ta z
  disjoint f th
  disjoint i th
  disjoint n th
  disjoint th z
  disjoint i j
  disjoint j n
  disjoint i ph
  assert |- ( ( th /\ ta ) -> _trCl ( X , A , R ) C_ B )

  proof
    wph
    wps
    wch
    wth
    wta
    wet
    wze
    wrh
    vy
    vz
    cA
    cB
    cD
    cR
    vf
    vi
    vj
    vn
    cK
    cX
    bnj1053.1
    bnj1053.2
    bnj1053.3
    bnj1053.4
    bnj1053.5
    bnj1053.6
    bnj1053.7
    bnj1053.8
    bnj1053.9
    bnj1053.10
    wth
    wta
    wch
    wze
    w-bnj17
    vn
    cv
    #
    cep
    wfr
    #
    wrh
    wet
    wi
    vi
    @0
    wral
    wth
    wta
    wch
    wze
    @1
    @0
    cD
    wcel
    #
    vf
    cv
    @0
    wfn
    wph
    wps
    @1
    wch
    bnj1053.3
    @2
    @0
    com
    wcel
    @0
    word
    @1
    cD
    vn
    bnj1053.7
    bnj923
    @0
    nnord
    @0
    ordfr
    3syl
    bnj769
    bnj707
    bnj1053.37
    jca
    bnj1052
end

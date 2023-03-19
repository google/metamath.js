include "cv.mm"
include "c1o.mm"
include "wceq.mm"
include "wcel.mm"
include "wa.mm"
include "w-bnj15.mm"
include "wfn.mm"
include "w3a.mm"
include "weu.mm"
include "wi.mm"
include "wex.mm"
include "wmo.mm"
include "bnj150.mm"
include "mpbi.mm"
include "bnj118.mm"
include "bnj149.mm"
include "eu5.mm"
include "sylanbrc.mm"
include "bnj130.mm"
include "mpbir.mm"
include "wsbc.mm"
include "sbceq1a.mm"
include "syl6bbr.mm"
include "mpbiri.mm"
include "a1d.mm"

theorem bnj151
  let wph: wff ph
  let wps: wff ps
  let wth: wff th
  let wta: wff ta
  let wze: wff ze
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cD: class D
  let cR: class R
  let vf: setvar f
  let vg: setvar g
  let vi: setvar i
  let vm: setvar m
  let vn: setvar n
  let cF: class F
  let bnjwphm: wff ph'
  let bnjwpsm: wff ps'
  let bnjwthm: wff th'
  let bnjwzem: wff ze'
  let bnjwphn: wff ph"
  let bnjwpsn: wff ps"
  let bnjwzen: wff ze"
  let bnjwth0: wff th0
  let bnjwze0: wff ze0
  let bnjwph1: wff ph1
  let bnjwps1: wff ps1
  let bnjwth1: wff th1
  let bnjwze1: wff ze1
  assume bnj151.1: |- ( ph <-> ( f ` (/) ) = _pred ( x , A , R ) )
  assume bnj151.2: |- ( ps <-> A. i e. _om ( suc i e. n -> ( f ` suc i ) = U_ y e. ( f ` i ) _pred ( y , A , R ) ) )
  assume bnj151.3: |- D = ( _om \ { (/) } )
  assume bnj151.4: |- ( th <-> ( ( R _FrSe A /\ x e. A ) -> E! f ( f Fn n /\ ph /\ ps ) ) )
  assume bnj151.5: |- ( ta <-> A. m e. D ( m _E n -> [. m / n ]. th ) )
  assume bnj151.6: |- ( ze <-> ( ( R _FrSe A /\ x e. A ) -> ( f Fn n /\ ph /\ ps ) ) )
  assume bnj151.7: |- ( ph' <-> [. 1o / n ]. ph )
  assume bnj151.8: |- ( ps' <-> [. 1o / n ]. ps )
  assume bnj151.9: |- ( th' <-> [. 1o / n ]. th )
  assume bnj151.10: |- ( th0 <-> ( ( R _FrSe A /\ x e. A ) -> E. f ( f Fn 1o /\ ph' /\ ps' ) ) )
  assume bnj151.11: |- ( th1 <-> ( ( R _FrSe A /\ x e. A ) -> E* f ( f Fn 1o /\ ph' /\ ps' ) ) )
  assume bnj151.12: |- ( ze' <-> [. 1o / n ]. ze )
  assume bnj151.13: |- F = { <. (/) , _pred ( x , A , R ) >. }
  assume bnj151.14: |- ( ph" <-> [. F / f ]. ph' )
  assume bnj151.15: |- ( ps" <-> [. F / f ]. ps' )
  assume bnj151.16: |- ( ze" <-> [. F / f ]. ze' )
  assume bnj151.17: |- ( ze0 <-> ( f Fn 1o /\ ph' /\ ps' ) )
  assume bnj151.18: |- ( ze1 <-> [. g / f ]. ze0 )
  assume bnj151.19: |- ( ph1 <-> [. g / f ]. ph' )
  assume bnj151.20: |- ( ps1 <-> [. g / f ]. ps' )

  disjoint A f
  disjoint A g
  disjoint A x
  disjoint f g
  disjoint f x
  disjoint g x
  disjoint A n
  disjoint f n
  disjoint n x
  disjoint F f
  disjoint F i
  disjoint F y
  disjoint f i
  disjoint f y
  disjoint i y
  disjoint R f
  disjoint R g
  disjoint R x
  disjoint R n
  disjoint f ze1
  disjoint f ze"
  disjoint g ze0
  disjoint i n
  disjoint n y
  disjoint m n
  assert |- ( n = 1o -> ( ( n e. D /\ ta ) -> th ) )

  proof
    vn
    cv
    #
    c1o
    wceq
    #
    wth
    @0
    cD
    wcel
    wta
    wa
    @1
    wth
    bnjwthm
    bnjwthm
    cA
    cR
    w-bnj15
    vx
    cv
    cA
    wcel
    wa
    #
    vf
    cv
    c1o
    wfn
    bnjwphm
    bnjwpsm
    w3a
    #
    vf
    weu
    #
    wi
    @2
    @3
    vf
    wex
    #
    @3
    vf
    wmo
    #
    @4
    bnjwth0
    @2
    @5
    wi
    wph
    wps
    wze
    vx
    vy
    cA
    cR
    vf
    vi
    vn
    cF
    bnjwphm
    bnjwpsm
    bnjwzem
    bnjwphn
    bnjwpsn
    bnjwzen
    bnjwth0
    bnj151.1
    bnj151.2
    bnj151.6
    bnj151.7
    bnj151.8
    bnj151.10
    bnj151.12
    bnj151.13
    bnj151.14
    bnj151.15
    bnj151.16
    bnj150
    bnj151.10
    mpbi
    bnjwth1
    @2
    @6
    wi
    vx
    cA
    cR
    vf
    vg
    bnjwphm
    bnjwpsm
    bnjwze0
    bnjwph1
    bnjwps1
    bnjwth1
    bnjwze1
    bnj151.11
    bnj151.17
    bnj151.18
    bnj151.19
    bnj151.20
    wph
    vx
    cA
    cR
    vf
    vn
    bnjwphm
    bnj151.1
    bnj151.7
    bnj118
    bnj149
    bnj151.11
    mpbi
    @3
    vf
    eu5
    sylanbrc
    wph
    wps
    wth
    vx
    cA
    cR
    vf
    vn
    bnjwphm
    bnjwpsm
    bnjwthm
    bnj151.4
    bnj151.7
    bnj151.8
    bnj151.9
    bnj130
    mpbir
    @1
    wth
    wth
    vn
    c1o
    wsbc
    bnjwthm
    wth
    vn
    c1o
    sbceq1a
    bnj151.9
    syl6bbr
    mpbiri
    a1d
end

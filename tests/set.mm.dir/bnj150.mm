include "wex.mm"
include "w-bnj15.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "c1o.mm"
include "wfn.mm"
include "w3a.mm"
include "wi.mm"
include "c0.mm"
include "c-bnj14.mm"
include "cop.mm"
include "csn.mm"
include "wfun.mm"
include "cvv.mm"
include "0ex.mm"
include "bnj93.mm"
include "funsng.mm"
include "sylancr.mm"
include "funeqi.mm"
include "sylibr.mm"
include "bnj96.mm"
include "bnj1422.mm"
include "cfv.mm"
include "wceq.mm"
include "bnj97.mm"
include "bnj125.mm"
include "jca.mm"
include "csuc.mm"
include "ciun.mm"
include "com.mm"
include "wral.mm"
include "bnj98.mm"
include "bnj126.mm"
include "mpbir.mm"
include "jctir.mm"
include "df-3an.mm"
include "bnj121.mm"
include "bnj124.mm"
include "bnj95.mm"
include "wsbc.mm"
include "sbceq1a.mm"
include "syl6bbr.mm"
include "spcev.mm"
include "ax-mp.mm"
include "19.37v.mm"
include "bitr4i.mm"
include "bnj133.mm"

theorem bnj150
  let wph: wff ph
  let wps: wff ps
  let wze: wff ze
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cR: class R
  let vf: setvar f
  let vi: setvar i
  let vn: setvar n
  let cF: class F
  let bnjwphm: wff ph'
  let bnjwpsm: wff ps'
  let bnjwzem: wff ze'
  let bnjwphn: wff ph"
  let bnjwpsn: wff ps"
  let bnjwzen: wff ze"
  let bnjwth0: wff th0
  assume bnj150.1: |- ( ph <-> ( f ` (/) ) = _pred ( x , A , R ) )
  assume bnj150.2: |- ( ps <-> A. i e. _om ( suc i e. n -> ( f ` suc i ) = U_ y e. ( f ` i ) _pred ( y , A , R ) ) )
  assume bnj150.3: |- ( ze <-> ( ( R _FrSe A /\ x e. A ) -> ( f Fn n /\ ph /\ ps ) ) )
  assume bnj150.4: |- ( ph' <-> [. 1o / n ]. ph )
  assume bnj150.5: |- ( ps' <-> [. 1o / n ]. ps )
  assume bnj150.6: |- ( th0 <-> ( ( R _FrSe A /\ x e. A ) -> E. f ( f Fn 1o /\ ph' /\ ps' ) ) )
  assume bnj150.7: |- ( ze' <-> [. 1o / n ]. ze )
  assume bnj150.8: |- F = { <. (/) , _pred ( x , A , R ) >. }
  assume bnj150.9: |- ( ph" <-> [. F / f ]. ph' )
  assume bnj150.10: |- ( ps" <-> [. F / f ]. ps' )
  assume bnj150.11: |- ( ze" <-> [. F / f ]. ze' )

  disjoint A f
  disjoint A n
  disjoint A x
  disjoint f n
  disjoint f x
  disjoint n x
  disjoint F f
  disjoint F i
  disjoint F y
  disjoint f i
  disjoint f y
  disjoint i y
  disjoint R f
  disjoint R n
  disjoint R x
  disjoint f ze"
  disjoint i n
  disjoint n y
  assert |- th0

  proof
    bnjwth0
    bnjwzem
    vf
    wex
    #
    bnjwzen
    @0
    bnjwzen
    cA
    cR
    w-bnj15
    vx
    cv
    #
    cA
    wcel
    wa
    #
    cF
    c1o
    wfn
    #
    bnjwphn
    bnjwpsn
    w3a
    #
    wi
    @2
    @3
    bnjwphn
    wa
    #
    bnjwpsn
    wa
    @4
    @2
    @5
    bnjwpsn
    @2
    @3
    bnjwphn
    @2
    cF
    c1o
    @2
    c0
    cA
    cR
    @1
    c-bnj14
    #
    cop
    csn
    #
    wfun
    #
    cF
    wfun
    @2
    c0
    cvv
    wcel
    @6
    cvv
    wcel
    @8
    0ex
    vx
    cA
    cR
    bnj93
    c0
    @6
    cvv
    cvv
    funsng
    sylancr
    cF
    @7
    bnj150.8
    funeqi
    sylibr
    vx
    cA
    cR
    cF
    bnj150.8
    bnj96
    bnj1422
    @2
    c0
    cF
    cfv
    @6
    wceq
    bnjwphn
    vx
    cA
    cR
    cF
    bnj150.8
    bnj97
    wph
    vx
    cA
    cR
    vf
    vn
    cF
    bnjwphm
    bnjwphn
    bnj150.1
    bnj150.4
    bnj150.9
    bnj150.8
    bnj125
    sylibr
    jca
    bnjwpsn
    vi
    cv
    #
    csuc
    #
    c1o
    wcel
    @10
    cF
    cfv
    vy
    @9
    cF
    cfv
    cA
    cR
    vy
    cv
    c-bnj14
    ciun
    wceq
    wi
    vi
    com
    wral
    vy
    cA
    cR
    vi
    cF
    bnj98
    wps
    vx
    vy
    cA
    cR
    vf
    vi
    vn
    cF
    bnjwpsm
    bnjwpsn
    bnj150.2
    bnj150.5
    bnj150.10
    bnj150.8
    bnj126
    mpbir
    jctir
    @3
    bnjwphn
    bnjwpsn
    df-3an
    sylibr
    vx
    cA
    cR
    vf
    cF
    bnjwphm
    bnjwpsm
    bnjwzem
    bnjwphn
    bnjwpsn
    bnjwzen
    bnj150.8
    bnj150.9
    bnj150.10
    bnj150.11
    wph
    wps
    wze
    vx
    cA
    cR
    vf
    vn
    bnjwphm
    bnjwpsm
    bnjwzem
    bnj150.3
    bnj150.7
    bnj150.4
    bnj150.5
    bnj121
    #
    bnj124
    mpbir
    bnjwzem
    bnjwzen
    vf
    cF
    vx
    cA
    cR
    cF
    bnj150.8
    bnj95
    vf
    cv
    #
    cF
    wceq
    bnjwzem
    bnjwzem
    vf
    cF
    wsbc
    bnjwzen
    bnjwzem
    vf
    cF
    sbceq1a
    bnj150.11
    syl6bbr
    spcev
    ax-mp
    bnjwth0
    @2
    @12
    c1o
    wfn
    bnjwphm
    bnjwpsm
    w3a
    #
    wi
    #
    bnjwzem
    vf
    bnjwth0
    @2
    @13
    vf
    wex
    wi
    @14
    vf
    wex
    bnj150.6
    @2
    @13
    vf
    19.37v
    bitr4i
    @11
    bnj133
    mpbir
end

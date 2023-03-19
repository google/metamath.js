include "wsbc.mm"
include "c1o.mm"
include "cv.mm"
include "csuc.mm"
include "wcel.mm"
include "cfv.mm"
include "c-bnj14.mm"
include "ciun.mm"
include "wceq.mm"
include "wi.mm"
include "com.mm"
include "wral.mm"
include "sbcbii.mm"
include "bnj95.mm"
include "bnj106.mm"
include "3bitri.mm"

theorem bnj126
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cR: class R
  let vf: setvar f
  let vi: setvar i
  let vn: setvar n
  let cF: class F
  let bnjwpsm: wff ps'
  let bnjwpsn: wff ps"
  assume bnj126.1: |- ( ps <-> A. i e. _om ( suc i e. n -> ( f ` suc i ) = U_ y e. ( f ` i ) _pred ( y , A , R ) ) )
  assume bnj126.2: |- ( ps' <-> [. 1o / n ]. ps )
  assume bnj126.3: |- ( ps" <-> [. F / f ]. ps' )
  assume bnj126.4: |- F = { <. (/) , _pred ( x , A , R ) >. }

  disjoint A f
  disjoint A n
  disjoint f n
  disjoint F f
  disjoint F i
  disjoint F y
  disjoint f i
  disjoint f y
  disjoint i y
  disjoint R f
  disjoint R n
  disjoint i n
  disjoint n y
  assert |- ( ps" <-> A. i e. _om ( suc i e. 1o -> ( F ` suc i ) = U_ y e. ( F ` i ) _pred ( y , A , R ) ) )

  proof
    bnjwpsn
    bnjwpsm
    vf
    cF
    wsbc
    wps
    vn
    c1o
    wsbc
    #
    vf
    cF
    wsbc
    vi
    cv
    #
    csuc
    #
    c1o
    wcel
    @2
    cF
    cfv
    vy
    @1
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
    bnj126.3
    bnjwpsm
    @0
    vf
    cF
    bnj126.2
    sbcbii
    wps
    vy
    cA
    cR
    vf
    vi
    vn
    cF
    bnj126.1
    vx
    cA
    cR
    cF
    bnj126.4
    bnj95
    bnj106
    3bitri
end

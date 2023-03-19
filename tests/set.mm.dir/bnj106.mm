include "c1o.mm"
include "wsbc.mm"
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
include "bnj105.mm"
include "bnj92.mm"
include "sbcbii.mm"
include "fveq1.mm"
include "bnj1113.mm"
include "eqeq12d.mm"
include "imbi2d.mm"
include "ralbidv.mm"
include "sbcie.mm"
include "bitri.mm"

theorem bnj106
  let wps: wff ps
  let vy: setvar y
  let cA: class A
  let cR: class R
  let vf: setvar f
  let vi: setvar i
  let vn: setvar n
  let cF: class F
  assume bnj106.1: |- ( ps <-> A. i e. _om ( suc i e. n -> ( f ` suc i ) = U_ y e. ( f ` i ) _pred ( y , A , R ) ) )
  assume bnj106.2: |- F e. _V

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
  assert |- ( [. F / f ]. [. 1o / n ]. ps <-> A. i e. _om ( suc i e. 1o -> ( F ` suc i ) = U_ y e. ( F ` i ) _pred ( y , A , R ) ) )

  proof
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
    #
    @2
    vf
    cv
    #
    cfv
    #
    vy
    @1
    @4
    cfv
    #
    cA
    cR
    vy
    cv
    c-bnj14
    #
    ciun
    #
    wceq
    #
    wi
    #
    vi
    com
    wral
    #
    vf
    cF
    wsbc
    @3
    @2
    cF
    cfv
    #
    vy
    @1
    cF
    cfv
    #
    @7
    ciun
    #
    wceq
    #
    wi
    #
    vi
    com
    wral
    #
    @0
    @11
    vf
    cF
    wps
    vy
    cA
    cR
    vf
    vi
    vn
    c1o
    bnj106.1
    bnj105
    bnj92
    sbcbii
    @11
    @17
    vf
    cF
    bnj106.2
    @4
    cF
    wceq
    #
    @10
    @16
    vi
    com
    @18
    @9
    @15
    @3
    @18
    @5
    @12
    @8
    @14
    @2
    @4
    cF
    fveq1
    vy
    @4
    cF
    @6
    @13
    @7
    @1
    @4
    cF
    fveq1
    bnj1113
    eqeq12d
    imbi2d
    ralbidv
    sbcie
    bitri
end

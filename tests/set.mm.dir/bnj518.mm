include "w-bnj15.mm"
include "cv.mm"
include "cfv.mm"
include "wss.mm"
include "c-bnj14.mm"
include "cvv.mm"
include "wcel.mm"
include "wral.mm"
include "com.mm"
include "w-bnj17.mm"
include "bnj334.mm"
include "bitri.mm"
include "w3a.mm"
include "wa.mm"
include "df-bnj17.mm"
include "bnj517.mm"
include "r19.21bi.mm"
include "sylbi.mm"
include "ssel.mm"
include "bnj93.mm"
include "ex.mm"
include "sylan9r.mm"
include "ralrimiv.mm"
include "sylan2.mm"

theorem bnj518
  let wph: wff ph
  let wps: wff ps
  let wta: wff ta
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cR: class R
  let vf: setvar f
  let vi: setvar i
  let vn: setvar n
  let vp: setvar p
  assume bnj518.1: |- ( ph <-> ( f ` (/) ) = _pred ( x , A , R ) )
  assume bnj518.2: |- ( ps <-> A. i e. _om ( suc i e. n -> ( f ` suc i ) = U_ y e. ( f ` i ) _pred ( y , A , R ) ) )
  assume bnj518.3: |- ( ta <-> ( ph /\ ps /\ n e. _om /\ p e. n ) )

  disjoint f i
  disjoint f p
  disjoint f y
  disjoint i p
  disjoint i y
  disjoint p y
  disjoint i n
  disjoint n p
  disjoint A i
  disjoint A p
  disjoint A y
  disjoint R y
  assert |- ( ( R _FrSe A /\ ta ) -> A. y e. ( f ` p ) _pred ( y , A , R ) e. _V )

  proof
    wta
    cA
    cR
    w-bnj15
    #
    vp
    cv
    #
    vf
    cv
    #
    cfv
    #
    cA
    wss
    #
    cA
    cR
    vy
    cv
    #
    c-bnj14
    cvv
    wcel
    #
    vy
    @3
    wral
    wta
    vn
    cv
    #
    com
    wcel
    #
    wph
    wps
    @1
    @7
    wcel
    #
    w-bnj17
    #
    @4
    wta
    wph
    wps
    @8
    @9
    w-bnj17
    @10
    bnj518.3
    wph
    wps
    @8
    @9
    bnj334
    bitri
    @10
    @8
    wph
    wps
    w3a
    #
    @9
    wa
    @4
    @8
    wph
    wps
    @9
    df-bnj17
    @11
    @4
    vp
    @7
    wph
    wps
    vy
    cA
    cR
    vi
    vp
    @2
    @7
    vx
    cv
    bnj518.1
    bnj518.2
    bnj517
    r19.21bi
    sylbi
    sylbi
    @0
    @4
    wa
    @6
    vy
    @3
    @4
    @5
    @3
    wcel
    @5
    cA
    wcel
    #
    @0
    @6
    @3
    cA
    @5
    ssel
    @0
    @12
    @6
    vy
    cA
    cR
    bnj93
    ex
    sylan9r
    ralrimiv
    sylan2
end

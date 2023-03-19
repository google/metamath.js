include "w-bnj15.mm"
include "cv.mm"
include "csn.mm"
include "cun.mm"
include "wceq.mm"
include "wfn.mm"
include "w-bnj17.mm"
include "wa.mm"
include "bnj422.mm"
include "bnj251.mm"
include "bitri.mm"
include "cfv.mm"
include "c-bnj14.mm"
include "ciun.mm"
include "cop.mm"
include "cvv.mm"
include "wcel.mm"
include "wfun.mm"
include "wral.mm"
include "fvex.mm"
include "bnj518.mm"
include "iunexg.mm"
include "sylancr.mm"
include "vex.mm"
include "bnj519.mm"
include "syl.mm"
include "cdm.mm"
include "dmsnopg.mm"
include "bnj1422.mm"
include "cin.mm"
include "c0.mm"
include "bnj521.mm"
include "fnun.mm"
include "mpan2.mm"
include "sylan2.mm"
include "fneq1i.mm"
include "sylibr.mm"
include "fneq2.mm"
include "syl5ibr.mm"
include "imp.mm"
include "sylbi.mm"

theorem bnj535
  let wta: wff ta
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cR: class R
  let vf: setvar f
  let vi: setvar i
  let vm: setvar m
  let vn: setvar n
  let cG: class G
  let vp: setvar p
  let bnjwphm: wff ph'
  let bnjwpsm: wff ps'
  assume bnj535.1: |- ( ph' <-> ( f ` (/) ) = _pred ( x , A , R ) )
  assume bnj535.2: |- ( ps' <-> A. i e. _om ( suc i e. m -> ( f ` suc i ) = U_ y e. ( f ` i ) _pred ( y , A , R ) ) )
  assume bnj535.3: |- G = ( f u. { <. m , U_ y e. ( f ` p ) _pred ( y , A , R ) >. } )
  assume bnj535.4: |- ( ta <-> ( ph' /\ ps' /\ m e. _om /\ p e. m ) )

  disjoint A i
  disjoint A p
  disjoint A y
  disjoint i p
  disjoint i y
  disjoint p y
  disjoint R i
  disjoint R p
  disjoint R y
  disjoint f i
  disjoint f p
  disjoint f y
  disjoint i m
  disjoint m p
  disjoint p ph'
  assert |- ( ( R _FrSe A /\ ta /\ n = ( m u. { m } ) /\ f Fn m ) -> G Fn n )

  proof
    cA
    cR
    w-bnj15
    #
    wta
    vn
    cv
    #
    vm
    cv
    #
    @2
    csn
    #
    cun
    #
    wceq
    #
    vf
    cv
    #
    @2
    wfn
    #
    w-bnj17
    #
    @5
    @7
    @0
    wta
    wa
    #
    wa
    #
    wa
    #
    cG
    @1
    wfn
    #
    @8
    @5
    @7
    @0
    wta
    w-bnj17
    @11
    @0
    wta
    @5
    @7
    bnj422
    @5
    @7
    @0
    wta
    bnj251
    bitri
    @5
    @10
    @12
    @10
    @12
    @5
    cG
    @4
    wfn
    #
    @10
    @6
    @2
    vy
    vp
    cv
    #
    @6
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
    cop
    csn
    #
    cun
    #
    @4
    wfn
    #
    @13
    @9
    @7
    @18
    @3
    wfn
    #
    @20
    @9
    @18
    @3
    @9
    @17
    cvv
    wcel
    #
    @18
    wfun
    @9
    @15
    cvv
    wcel
    @16
    cvv
    wcel
    vy
    @15
    wral
    @22
    @14
    @6
    fvex
    bnjwphm
    bnjwpsm
    wta
    vx
    vy
    cA
    cR
    vf
    vi
    vm
    vp
    bnj535.1
    bnj535.2
    bnj535.4
    bnj518
    vy
    @15
    @16
    cvv
    cvv
    iunexg
    sylancr
    #
    @2
    @17
    vm
    vex
    bnj519
    syl
    @9
    @22
    @18
    cdm
    @3
    wceq
    @23
    @2
    @17
    cvv
    dmsnopg
    syl
    bnj1422
    @7
    @21
    wa
    @2
    @3
    cin
    c0
    wceq
    @20
    @2
    bnj521
    @2
    @3
    @6
    @18
    fnun
    mpan2
    sylan2
    @4
    cG
    @19
    bnj535.3
    fneq1i
    sylibr
    @1
    @4
    cG
    fneq2
    syl5ibr
    imp
    sylbi
end

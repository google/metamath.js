include "cv.mm"
include "c1st.mm"
include "cfv.mm"
include "crn.mm"
include "wne.mm"
include "c2nd.mm"
include "co.mm"
include "wcel.mm"
include "wral.mm"
include "wss.mm"
include "wo.mm"
include "wi.mm"
include "cidl.mm"
include "wa.mm"
include "crab.mm"
include "crngo.mm"
include "cpridl.mm"
include "wceq.mm"
include "fveq2.mm"
include "syl6eqr.mm"
include "rneqd.mm"
include "neeq2d.mm"
include "oveqd.mm"
include "eleq1d.mm"
include "2ralbidv.mm"
include "imbi1d.mm"
include "raleqbidv.mm"
include "anbi12d.mm"
include "rabeqbidv.mm"
include "df-pridl.mm"
include "fvex.mm"
include "rabex.mm"
include "fvmpt.mm"

theorem pridlval
  let vx: setvar x
  let vy: setvar y
  let cR: class R
  let vi: setvar i
  let cG: class G
  let cH: class H
  let cX: class X
  let va: setvar a
  let vb: setvar b
  let vr: setvar r
  assume pridlval.1: |- G = ( 1st ` R )
  assume pridlval.2: |- H = ( 2nd ` R )
  assume pridlval.3: |- X = ran G

  disjoint R i
  disjoint R x
  disjoint R y
  disjoint R a
  disjoint R b
  disjoint i x
  disjoint i y
  disjoint a i
  disjoint b i
  disjoint x y
  disjoint a x
  disjoint b x
  disjoint a y
  disjoint b y
  disjoint a b
  disjoint X i
  disjoint H i
  disjoint R r
  disjoint i r
  disjoint r x
  disjoint r y
  disjoint a r
  disjoint b r
  disjoint X r
  disjoint H r
  assert |- ( R e. RingOps -> ( PrIdl ` R ) = { i e. ( Idl ` R ) | ( i =/= X /\ A. a e. ( Idl ` R ) A. b e. ( Idl ` R ) ( A. x e. a A. y e. b ( x H y ) e. i -> ( a C_ i \/ b C_ i ) ) ) } )

  proof
    vr
    cR
    vi
    cv
    #
    vr
    cv
    #
    c1st
    cfv
    #
    crn
    #
    wne
    #
    vx
    cv
    #
    vy
    cv
    #
    @1
    c2nd
    cfv
    #
    co
    #
    @0
    wcel
    #
    vy
    vb
    cv
    #
    wral
    vx
    va
    cv
    #
    wral
    #
    @11
    @0
    wss
    @10
    @0
    wss
    wo
    #
    wi
    #
    vb
    @1
    cidl
    cfv
    #
    wral
    #
    va
    @15
    wral
    #
    wa
    #
    vi
    @15
    crab
    @0
    cX
    wne
    #
    @5
    @6
    cH
    co
    #
    @0
    wcel
    #
    vy
    @10
    wral
    vx
    @11
    wral
    #
    @13
    wi
    #
    vb
    cR
    cidl
    cfv
    #
    wral
    #
    va
    @24
    wral
    #
    wa
    #
    vi
    @24
    crab
    crngo
    cpridl
    @1
    cR
    wceq
    #
    @18
    @27
    vi
    @15
    @24
    @1
    cR
    cidl
    fveq2
    #
    @28
    @4
    @19
    @17
    @26
    @28
    @3
    cX
    @0
    @28
    @3
    cG
    crn
    cX
    @28
    @2
    cG
    @28
    @2
    cR
    c1st
    cfv
    cG
    @1
    cR
    c1st
    fveq2
    pridlval.1
    syl6eqr
    rneqd
    pridlval.3
    syl6eqr
    neeq2d
    @28
    @16
    @25
    va
    @15
    @24
    @29
    @28
    @14
    @23
    vb
    @15
    @24
    @29
    @28
    @12
    @22
    @13
    @28
    @9
    @21
    vx
    vy
    @11
    @10
    @28
    @8
    @20
    @0
    @28
    @7
    cH
    @5
    @6
    @28
    @7
    cR
    c2nd
    cfv
    cH
    @1
    cR
    c2nd
    fveq2
    pridlval.2
    syl6eqr
    oveqd
    eleq1d
    2ralbidv
    imbi1d
    raleqbidv
    raleqbidv
    anbi12d
    rabeqbidv
    vx
    vy
    vi
    vr
    va
    vb
    df-pridl
    @27
    vi
    @24
    cR
    cidl
    fvex
    rabex
    fvmpt
end

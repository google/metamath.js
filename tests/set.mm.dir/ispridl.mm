include "crngo.mm"
include "wcel.mm"
include "cpridl.mm"
include "cfv.mm"
include "cv.mm"
include "wne.mm"
include "co.mm"
include "wral.mm"
include "wss.mm"
include "wo.mm"
include "wi.mm"
include "cidl.mm"
include "wa.mm"
include "crab.mm"
include "w3a.mm"
include "pridlval.mm"
include "eleq2d.mm"
include "wceq.mm"
include "neeq1.mm"
include "eleq2.mm"
include "2ralbidv.mm"
include "sseq2.mm"
include "orbi12d.mm"
include "imbi12d.mm"
include "anbi12d.mm"
include "elrab.mm"
include "3anass.mm"
include "bitr4i.mm"
include "syl6bb.mm"

theorem ispridl
  let vx: setvar x
  let vy: setvar y
  let cP: class P
  let cR: class R
  let cG: class G
  let cH: class H
  let cX: class X
  let va: setvar a
  let vb: setvar b
  let vr: setvar r
  let vi: setvar i
  assume pridlval.1: |- G = ( 1st ` R )
  assume pridlval.2: |- H = ( 2nd ` R )
  assume pridlval.3: |- X = ran G

  disjoint R x
  disjoint R y
  disjoint R a
  disjoint R b
  disjoint x y
  disjoint a x
  disjoint b x
  disjoint a y
  disjoint b y
  disjoint a b
  disjoint P x
  disjoint P y
  disjoint P a
  disjoint P b
  disjoint R r
  disjoint R i
  disjoint i r
  disjoint r x
  disjoint r y
  disjoint a r
  disjoint b r
  disjoint i x
  disjoint i y
  disjoint a i
  disjoint b i
  disjoint X i
  disjoint X r
  disjoint H i
  disjoint H r
  disjoint P i
  assert |- ( R e. RingOps -> ( P e. ( PrIdl ` R ) <-> ( P e. ( Idl ` R ) /\ P =/= X /\ A. a e. ( Idl ` R ) A. b e. ( Idl ` R ) ( A. x e. a A. y e. b ( x H y ) e. P -> ( a C_ P \/ b C_ P ) ) ) ) )

  proof
    cR
    crngo
    wcel
    #
    cP
    cR
    cpridl
    cfv
    #
    wcel
    cP
    vi
    cv
    #
    cX
    wne
    #
    vx
    cv
    vy
    cv
    cH
    co
    #
    @2
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
    @7
    @2
    wss
    #
    @6
    @2
    wss
    #
    wo
    #
    wi
    #
    vb
    cR
    cidl
    cfv
    #
    wral
    va
    @13
    wral
    #
    wa
    #
    vi
    @13
    crab
    #
    wcel
    #
    cP
    @13
    wcel
    #
    cP
    cX
    wne
    #
    @4
    cP
    wcel
    #
    vy
    @6
    wral
    vx
    @7
    wral
    #
    @7
    cP
    wss
    #
    @6
    cP
    wss
    #
    wo
    #
    wi
    #
    vb
    @13
    wral
    va
    @13
    wral
    #
    w3a
    #
    @0
    @1
    @16
    cP
    vx
    vy
    cR
    vi
    cG
    cH
    cX
    va
    vb
    pridlval.1
    pridlval.2
    pridlval.3
    pridlval
    eleq2d
    @17
    @18
    @19
    @26
    wa
    #
    wa
    @27
    @15
    @28
    vi
    cP
    @13
    @2
    cP
    wceq
    #
    @3
    @19
    @14
    @26
    @2
    cP
    cX
    neeq1
    @29
    @12
    @25
    va
    vb
    @13
    @13
    @29
    @8
    @21
    @11
    @24
    @29
    @5
    @20
    vx
    vy
    @7
    @6
    @2
    cP
    @4
    eleq2
    2ralbidv
    @29
    @9
    @22
    @10
    @23
    @2
    cP
    @7
    sseq2
    @2
    cP
    @6
    sseq2
    orbi12d
    imbi12d
    2ralbidv
    anbi12d
    elrab
    @18
    @19
    @26
    3anass
    bitr4i
    syl6bb
end

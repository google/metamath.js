include "wcel.mm"
include "cv.mm"
include "wf1o.mm"
include "wss.mm"
include "cfv.mm"
include "wb.mm"
include "wral.mm"
include "wa.mm"
include "cab.mm"
include "pautsetN.mm"
include "eleq2d.mm"
include "cvv.mm"
include "wf.mm"
include "f1of.mm"
include "cpsubsp.mm"
include "fvex.mm"
include "eqeltri.mm"
include "fex.mm"
include "sylancl.mm"
include "adantr.mm"
include "wceq.mm"
include "f1oeq1.mm"
include "fveq1.mm"
include "sseq12d.mm"
include "bibi2d.mm"
include "2ralbidv.mm"
include "anbi12d.mm"
include "elab3.mm"
include "syl6bb.mm"

theorem ispautN
  let vx: setvar x
  let vy: setvar y
  let cB: class B
  let cS: class S
  let cF: class F
  let cK: class K
  let cM: class M
  let vf: setvar f
  let vk: setvar k
  assume pautset.s: |- S = ( PSubSp ` K )
  assume pautset.m: |- M = ( PAut ` K )

  disjoint x y
  disjoint F x
  disjoint F y
  disjoint K x
  disjoint S x
  disjoint S y
  disjoint f x
  disjoint f y
  disjoint F f
  disjoint f k
  disjoint K f
  disjoint k x
  disjoint K k
  disjoint S f
  disjoint k y
  disjoint S k
  assert |- ( K e. B -> ( F e. M <-> ( F : S -1-1-onto-> S /\ A. x e. S A. y e. S ( x C_ y <-> ( F ` x ) C_ ( F ` y ) ) ) ) )

  proof
    cK
    cB
    wcel
    #
    cF
    cM
    wcel
    cF
    cS
    cS
    vf
    cv
    #
    wf1o
    #
    vx
    cv
    #
    vy
    cv
    #
    wss
    #
    @3
    @1
    cfv
    #
    @4
    @1
    cfv
    #
    wss
    #
    wb
    #
    vy
    cS
    wral
    vx
    cS
    wral
    #
    wa
    #
    vf
    cab
    #
    wcel
    cS
    cS
    cF
    wf1o
    #
    @5
    @3
    cF
    cfv
    #
    @4
    cF
    cfv
    #
    wss
    #
    wb
    #
    vy
    cS
    wral
    vx
    cS
    wral
    #
    wa
    #
    @0
    cM
    @12
    cF
    vx
    vy
    cB
    cS
    vf
    cK
    cM
    pautset.s
    pautset.m
    pautsetN
    eleq2d
    @11
    @19
    vf
    cF
    @13
    cF
    cvv
    wcel
    #
    @18
    @13
    cS
    cS
    cF
    wf
    cS
    cvv
    wcel
    @20
    cS
    cS
    cF
    f1of
    cS
    cK
    cpsubsp
    cfv
    cvv
    pautset.s
    cK
    cpsubsp
    fvex
    eqeltri
    cS
    cS
    cvv
    cF
    fex
    sylancl
    adantr
    @1
    cF
    wceq
    #
    @2
    @13
    @10
    @18
    cS
    cS
    @1
    cF
    f1oeq1
    @21
    @9
    @17
    vx
    vy
    cS
    cS
    @21
    @8
    @16
    @5
    @21
    @6
    @14
    @7
    @15
    @3
    @1
    cF
    fveq1
    @4
    @1
    cF
    fveq1
    sseq12d
    bibi2d
    2ralbidv
    anbi12d
    elab3
    syl6bb
end

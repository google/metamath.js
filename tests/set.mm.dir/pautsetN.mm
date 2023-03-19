include "wcel.mm"
include "cvv.mm"
include "cv.mm"
include "wf1o.mm"
include "wss.mm"
include "cfv.mm"
include "wb.mm"
include "wral.mm"
include "wa.mm"
include "cab.mm"
include "wceq.mm"
include "elex.mm"
include "cpautN.mm"
include "cpsubsp.mm"
include "fveq2.mm"
include "syl6eqr.mm"
include "f1oeq2.mm"
include "syl.mm"
include "f1oeq3.mm"
include "bitrd.mm"
include "raleqdv.mm"
include "raleqbidv.mm"
include "anbi12d.mm"
include "abbidv.mm"
include "df-pautN.mm"
include "wf.mm"
include "cmap.mm"
include "co.mm"
include "fvex.mm"
include "eqeltri.mm"
include "mapval.mm"
include "ovex.mm"
include "eqeltrri.mm"
include "f1of.mm"
include "ss2abi.mm"
include "ssexi.mm"
include "simpl.mm"
include "fvmpt.mm"
include "syl5eq.mm"

theorem pautsetN
  let vx: setvar x
  let vy: setvar y
  let cB: class B
  let cS: class S
  let vf: setvar f
  let cK: class K
  let cM: class M
  let cF: class F
  let vk: setvar k
  assume pautset.s: |- S = ( PSubSp ` K )
  assume pautset.m: |- M = ( PAut ` K )

  disjoint f x
  disjoint f y
  disjoint x y
  disjoint K f
  disjoint K x
  disjoint S f
  disjoint S x
  disjoint S y
  disjoint F f
  disjoint F x
  disjoint F y
  disjoint f k
  disjoint k x
  disjoint K k
  disjoint k y
  disjoint S k
  assert |- ( K e. B -> M = { f | ( f : S -1-1-onto-> S /\ A. x e. S A. y e. S ( x C_ y <-> ( f ` x ) C_ ( f ` y ) ) ) } )

  proof
    cK
    cB
    wcel
    cK
    cvv
    wcel
    #
    cM
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
    @3
    @1
    cfv
    @4
    @1
    cfv
    wss
    wb
    #
    vy
    cS
    wral
    #
    vx
    cS
    wral
    #
    wa
    #
    vf
    cab
    #
    wceq
    cK
    cB
    elex
    @0
    cM
    cK
    cpautN
    cfv
    @9
    pautset.m
    vk
    cK
    vk
    cv
    #
    cpsubsp
    cfv
    #
    @11
    @1
    wf1o
    #
    @5
    vy
    @11
    wral
    #
    vx
    @11
    wral
    #
    wa
    #
    vf
    cab
    @9
    cvv
    cpautN
    @10
    cK
    wceq
    #
    @15
    @8
    vf
    @16
    @12
    @2
    @14
    @7
    @16
    @12
    cS
    @11
    @1
    wf1o
    #
    @2
    @16
    @11
    cS
    wceq
    #
    @12
    @17
    wb
    @16
    @11
    cK
    cpsubsp
    cfv
    #
    cS
    @10
    cK
    cpsubsp
    fveq2
    pautset.s
    syl6eqr
    #
    @11
    cS
    @11
    @1
    f1oeq2
    syl
    @16
    @18
    @17
    @2
    wb
    @20
    @11
    cS
    cS
    @1
    f1oeq3
    syl
    bitrd
    @16
    @13
    @6
    vx
    @11
    cS
    @20
    @16
    @5
    vy
    @11
    cS
    @20
    raleqdv
    raleqbidv
    anbi12d
    abbidv
    vx
    vy
    vf
    vk
    df-pautN
    @9
    @2
    vf
    cab
    #
    @21
    cS
    cS
    @1
    wf
    #
    vf
    cab
    #
    cS
    cS
    cmap
    co
    @23
    cvv
    cS
    cS
    vf
    cS
    @19
    cvv
    pautset.s
    cK
    cpsubsp
    fvex
    eqeltri
    #
    @24
    mapval
    cS
    cS
    cmap
    ovex
    eqeltrri
    @2
    @22
    vf
    cS
    cS
    @1
    f1of
    ss2abi
    ssexi
    @8
    @2
    vf
    @2
    @7
    simpl
    ss2abi
    ssexi
    fvmpt
    syl5eq
    syl
end

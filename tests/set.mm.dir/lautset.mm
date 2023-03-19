include "wcel.mm"
include "cvv.mm"
include "cv.mm"
include "wf1o.mm"
include "wbr.mm"
include "cfv.mm"
include "wb.mm"
include "wral.mm"
include "wa.mm"
include "cab.mm"
include "wceq.mm"
include "elex.mm"
include "claut.mm"
include "cbs.mm"
include "cple.mm"
include "fveq2.mm"
include "syl6eqr.mm"
include "f1oeq2.mm"
include "syl.mm"
include "f1oeq3.mm"
include "bitrd.mm"
include "breqd.mm"
include "bibi12d.mm"
include "raleqbidv.mm"
include "anbi12d.mm"
include "abbidv.mm"
include "df-laut.mm"
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

theorem lautset
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let vf: setvar f
  let cI: class I
  let cK: class K
  let c.le: class .<_
  let vk: setvar k
  let cF: class F
  assume lautset.b: |- B = ( Base ` K )
  assume lautset.l: |- .<_ = ( le ` K )
  assume lautset.i: |- I = ( LAut ` K )

  disjoint f x
  disjoint f y
  disjoint B f
  disjoint x y
  disjoint B x
  disjoint B y
  disjoint K f
  disjoint K x
  disjoint K y
  disjoint .<_ f
  disjoint f k
  disjoint k x
  disjoint k y
  disjoint B k
  disjoint F f
  disjoint F x
  disjoint F y
  disjoint K k
  disjoint .<_ k
  assert |- ( K e. A -> I = { f | ( f : B -1-1-onto-> B /\ A. x e. B A. y e. B ( x .<_ y <-> ( f ` x ) .<_ ( f ` y ) ) ) } )

  proof
    cK
    cA
    wcel
    cK
    cvv
    wcel
    #
    cI
    cB
    cB
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
    c.le
    wbr
    #
    @3
    @1
    cfv
    #
    @4
    @1
    cfv
    #
    c.le
    wbr
    #
    wb
    #
    vy
    cB
    wral
    #
    vx
    cB
    wral
    #
    wa
    #
    vf
    cab
    #
    wceq
    cK
    cA
    elex
    @0
    cI
    cK
    claut
    cfv
    @13
    lautset.i
    vk
    cK
    vk
    cv
    #
    cbs
    cfv
    #
    @15
    @1
    wf1o
    #
    @3
    @4
    @14
    cple
    cfv
    #
    wbr
    #
    @6
    @7
    @17
    wbr
    #
    wb
    #
    vy
    @15
    wral
    #
    vx
    @15
    wral
    #
    wa
    #
    vf
    cab
    @13
    cvv
    claut
    @14
    cK
    wceq
    #
    @23
    @12
    vf
    @24
    @16
    @2
    @22
    @11
    @24
    @16
    cB
    @15
    @1
    wf1o
    #
    @2
    @24
    @15
    cB
    wceq
    #
    @16
    @25
    wb
    @24
    @15
    cK
    cbs
    cfv
    #
    cB
    @14
    cK
    cbs
    fveq2
    lautset.b
    syl6eqr
    #
    @15
    cB
    @15
    @1
    f1oeq2
    syl
    @24
    @26
    @25
    @2
    wb
    @28
    @15
    cB
    cB
    @1
    f1oeq3
    syl
    bitrd
    @24
    @21
    @10
    vx
    @15
    cB
    @28
    @24
    @20
    @9
    vy
    @15
    cB
    @28
    @24
    @18
    @5
    @19
    @8
    @24
    @17
    c.le
    @3
    @4
    @24
    @17
    cK
    cple
    cfv
    c.le
    @14
    cK
    cple
    fveq2
    lautset.l
    syl6eqr
    #
    breqd
    @24
    @17
    c.le
    @6
    @7
    @29
    breqd
    bibi12d
    raleqbidv
    raleqbidv
    anbi12d
    abbidv
    vx
    vy
    vf
    vk
    df-laut
    @13
    @2
    vf
    cab
    #
    @30
    cB
    cB
    @1
    wf
    #
    vf
    cab
    #
    cB
    cB
    cmap
    co
    @32
    cvv
    cB
    cB
    vf
    cB
    @27
    cvv
    lautset.b
    cK
    cbs
    fvex
    eqeltri
    #
    @33
    mapval
    cB
    cB
    cmap
    ovex
    eqeltrri
    @2
    @31
    vf
    cB
    cB
    @1
    f1of
    ss2abi
    ssexi
    @12
    @2
    vf
    @2
    @11
    simpl
    ss2abi
    ssexi
    fvmpt
    syl5eq
    syl
end

include "wcel.mm"
include "cv.mm"
include "wf1o.mm"
include "wbr.mm"
include "cfv.mm"
include "wb.mm"
include "wral.mm"
include "wa.mm"
include "cab.mm"
include "lautset.mm"
include "eleq2d.mm"
include "cvv.mm"
include "wf.mm"
include "f1of.mm"
include "cbs.mm"
include "fvex.mm"
include "eqeltri.mm"
include "fex.mm"
include "sylancl.mm"
include "adantr.mm"
include "wceq.mm"
include "f1oeq1.mm"
include "fveq1.mm"
include "breq12d.mm"
include "bibi2d.mm"
include "2ralbidv.mm"
include "anbi12d.mm"
include "elab3.mm"
include "syl6bb.mm"

theorem islaut
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cF: class F
  let cI: class I
  let cK: class K
  let c.le: class .<_
  let vf: setvar f
  let vk: setvar k
  assume lautset.b: |- B = ( Base ` K )
  assume lautset.l: |- .<_ = ( le ` K )
  assume lautset.i: |- I = ( LAut ` K )

  disjoint x y
  disjoint B x
  disjoint B y
  disjoint F x
  disjoint F y
  disjoint K x
  disjoint K y
  disjoint f k
  disjoint f x
  disjoint f y
  disjoint B f
  disjoint k x
  disjoint k y
  disjoint B k
  disjoint F f
  disjoint K f
  disjoint K k
  disjoint .<_ f
  disjoint .<_ k
  assert |- ( K e. A -> ( F e. I <-> ( F : B -1-1-onto-> B /\ A. x e. B A. y e. B ( x .<_ y <-> ( F ` x ) .<_ ( F ` y ) ) ) ) )

  proof
    cK
    cA
    wcel
    #
    cF
    cI
    wcel
    cF
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
    vx
    cB
    wral
    #
    wa
    #
    vf
    cab
    #
    wcel
    cB
    cB
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
    c.le
    wbr
    #
    wb
    #
    vy
    cB
    wral
    vx
    cB
    wral
    #
    wa
    #
    @0
    cI
    @12
    cF
    vx
    vy
    cA
    cB
    vf
    cI
    cK
    c.le
    lautset.b
    lautset.l
    lautset.i
    lautset
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
    cB
    cB
    cF
    wf
    cB
    cvv
    wcel
    @20
    cB
    cB
    cF
    f1of
    cB
    cK
    cbs
    cfv
    cvv
    lautset.b
    cK
    cbs
    fvex
    eqeltri
    cB
    cB
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
    cB
    cB
    @1
    cF
    f1oeq1
    @21
    @9
    @17
    vx
    vy
    cB
    cB
    @21
    @8
    @16
    @5
    @21
    @6
    @14
    @7
    @15
    c.le
    @3
    @1
    cF
    fveq1
    @4
    @1
    cF
    fveq1
    breq12d
    bibi2d
    2ralbidv
    anbi12d
    elab3
    syl6bb
end

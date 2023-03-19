include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "cfv.mm"
include "cv.mm"
include "wceq.mm"
include "crio.mm"
include "copab.mm"
include "cvv.mm"
include "cxp.mm"
include "c1st.mm"
include "c2nd.mm"
include "dicval.mm"
include "eleq2d.mm"
include "cop.mm"
include "vex.mm"
include "op1std.mm"
include "op2ndd.mm"
include "fveq1d.mm"
include "eqeq12d.mm"
include "eleq1d.mm"
include "anbi12d.mm"
include "elopaba.mm"
include "syl6bb.mm"

theorem dicelvalN
  let cA: class A
  let cP: class P
  let cQ: class Q
  let cT: class T
  let vg: setvar g
  let cE: class E
  let cH: class H
  let cI: class I
  let cK: class K
  let c.le: class .<_
  let cV: class V
  let cW: class W
  let cY: class Y
  let vs: setvar s
  let vf: setvar f
  let vk: setvar k
  let vr: setvar r
  let vw: setvar w
  let vq: setvar q
  assume dicval.l: |- .<_ = ( le ` K )
  assume dicval.a: |- A = ( Atoms ` K )
  assume dicval.h: |- H = ( LHyp ` K )
  assume dicval.p: |- P = ( ( oc ` K ) ` W )
  assume dicval.t: |- T = ( ( LTrn ` K ) ` W )
  assume dicval.e: |- E = ( ( TEndo ` K ) ` W )
  assume dicval.i: |- I = ( ( DIsoC ` K ) ` W )

  disjoint K g
  disjoint T g
  disjoint W g
  disjoint Q g
  disjoint P s
  disjoint T s
  disjoint f s
  disjoint Y f
  disjoint Y s
  disjoint .<_ k
  disjoint k r
  disjoint A k
  disjoint A r
  disjoint k w
  disjoint H k
  disjoint H w
  disjoint f g
  disjoint f k
  disjoint f q
  disjoint f r
  disjoint f s
  disjoint f w
  disjoint K f
  disjoint g k
  disjoint g q
  disjoint g r
  disjoint g s
  disjoint g w
  disjoint k q
  disjoint k s
  disjoint K k
  disjoint q r
  disjoint q s
  disjoint q w
  disjoint K q
  disjoint r s
  disjoint r w
  disjoint K r
  disjoint s w
  disjoint K s
  disjoint K w
  disjoint .<_ q
  disjoint .<_ w
  disjoint A q
  disjoint A w
  disjoint E w
  disjoint P w
  disjoint T w
  disjoint W f
  disjoint W q
  disjoint W r
  disjoint W s
  disjoint W w
  disjoint .<_ r
  disjoint E f
  disjoint E q
  disjoint E s
  disjoint P f
  disjoint P q
  disjoint Q f
  disjoint Q q
  disjoint Q r
  disjoint Q s
  disjoint T f
  disjoint T q
  assert |- ( ( ( K e. V /\ W e. H ) /\ ( Q e. A /\ -. Q .<_ W ) ) -> ( Y e. ( I ` Q ) <-> ( Y e. ( _V X. _V ) /\ ( ( 1st ` Y ) = ( ( 2nd ` Y ) ` ( iota_ g e. T ( g ` P ) = Q ) ) /\ ( 2nd ` Y ) e. E ) ) ) )

  proof
    cK
    cV
    wcel
    cW
    cH
    wcel
    wa
    cQ
    cA
    wcel
    cQ
    cW
    c.le
    wbr
    wn
    wa
    wa
    #
    cY
    cQ
    cI
    cfv
    #
    wcel
    cY
    vf
    cv
    #
    cP
    vg
    cv
    cfv
    cQ
    wceq
    vg
    cT
    crio
    #
    vs
    cv
    #
    cfv
    #
    wceq
    #
    @4
    cE
    wcel
    #
    wa
    #
    vf
    vs
    copab
    #
    wcel
    cY
    cvv
    cvv
    cxp
    wcel
    cY
    c1st
    cfv
    #
    @3
    cY
    c2nd
    cfv
    #
    cfv
    #
    wceq
    #
    @11
    cE
    wcel
    #
    wa
    #
    wa
    @0
    @1
    @9
    cY
    cA
    cP
    cQ
    cT
    vf
    vg
    cE
    cH
    cI
    cK
    c.le
    cV
    cW
    vs
    dicval.l
    dicval.a
    dicval.h
    dicval.p
    dicval.t
    dicval.e
    dicval.i
    dicval
    eleq2d
    @15
    @8
    vf
    vs
    cY
    cY
    @2
    @4
    cop
    wceq
    #
    @13
    @6
    @14
    @7
    @16
    @10
    @2
    @12
    @5
    @2
    @4
    cY
    vf
    vex
    #
    vs
    vex
    #
    op1std
    @16
    @3
    @11
    @4
    @2
    @4
    cY
    @17
    @18
    op2ndd
    #
    fveq1d
    eqeq12d
    @16
    @11
    @4
    cE
    @19
    eleq1d
    anbi12d
    elopaba
    syl6bb
end

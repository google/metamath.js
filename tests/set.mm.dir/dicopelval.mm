include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "cop.mm"
include "cfv.mm"
include "cv.mm"
include "wceq.mm"
include "crio.mm"
include "copab.mm"
include "dicval.mm"
include "eleq2d.mm"
include "eqeq1.mm"
include "anbi1d.mm"
include "fveq1.mm"
include "eqeq2d.mm"
include "eleq1.mm"
include "anbi12d.mm"
include "opelopab.mm"
include "syl6bb.mm"

theorem dicopelval
  let cA: class A
  let cP: class P
  let cQ: class Q
  let cS: class S
  let cT: class T
  let vg: setvar g
  let cE: class E
  let cF: class F
  let cH: class H
  let cI: class I
  let cK: class K
  let c.le: class .<_
  let cV: class V
  let cW: class W
  let vf: setvar f
  let vs: setvar s
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
  assume dicelval.f: |- F e. _V
  assume dicelval.s: |- S e. _V

  disjoint K g
  disjoint T g
  disjoint W g
  disjoint Q g
  disjoint f s
  disjoint F f
  disjoint F s
  disjoint P s
  disjoint S f
  disjoint S s
  disjoint T s
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
  assert |- ( ( ( K e. V /\ W e. H ) /\ ( Q e. A /\ -. Q .<_ W ) ) -> ( <. F , S >. e. ( I ` Q ) <-> ( F = ( S ` ( iota_ g e. T ( g ` P ) = Q ) ) /\ S e. E ) ) )

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
    cF
    cS
    cop
    #
    cQ
    cI
    cfv
    #
    wcel
    @1
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
    @5
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
    cF
    @4
    cS
    cfv
    #
    wceq
    #
    cS
    cE
    wcel
    #
    wa
    #
    @0
    @2
    @10
    @1
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
    @9
    cF
    @6
    wceq
    #
    @8
    wa
    @14
    vf
    vs
    cF
    cS
    dicelval.f
    dicelval.s
    @3
    cF
    wceq
    @7
    @15
    @8
    @3
    cF
    @6
    eqeq1
    anbi1d
    @5
    cS
    wceq
    #
    @15
    @12
    @8
    @13
    @16
    @6
    @11
    cF
    @4
    @5
    cS
    fveq1
    eqeq2d
    @5
    cS
    cE
    eleq1
    anbi12d
    opelopab
    syl6bb
end

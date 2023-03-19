include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "cfv.mm"
include "cvv.mm"
include "cxp.mm"
include "c1st.mm"
include "cv.mm"
include "wceq.mm"
include "crio.mm"
include "c2nd.mm"
include "dicelvalN.mm"
include "fveq2i.mm"
include "eqeq2i.mm"
include "anbi1i.mm"
include "anbi2i.mm"
include "syl6bbr.mm"

theorem dicelval2N
  let cA: class A
  let cP: class P
  let cQ: class Q
  let cT: class T
  let vg: setvar g
  let cE: class E
  let cG: class G
  let cH: class H
  let cI: class I
  let cK: class K
  let c.le: class .<_
  let cV: class V
  let cW: class W
  let cY: class Y
  let vk: setvar k
  let vr: setvar r
  let vw: setvar w
  let vf: setvar f
  let vq: setvar q
  let vs: setvar s
  assume dicval.l: |- .<_ = ( le ` K )
  assume dicval.a: |- A = ( Atoms ` K )
  assume dicval.h: |- H = ( LHyp ` K )
  assume dicval.p: |- P = ( ( oc ` K ) ` W )
  assume dicval.t: |- T = ( ( LTrn ` K ) ` W )
  assume dicval.e: |- E = ( ( TEndo ` K ) ` W )
  assume dicval.i: |- I = ( ( DIsoC ` K ) ` W )
  assume dicval2.g: |- G = ( iota_ g e. T ( g ` P ) = Q )

  disjoint K g
  disjoint T g
  disjoint W g
  disjoint Q g
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
  disjoint G f
  disjoint Y f
  disjoint Y s
  assert |- ( ( ( K e. V /\ W e. H ) /\ ( Q e. A /\ -. Q .<_ W ) ) -> ( Y e. ( I ` Q ) <-> ( Y e. ( _V X. _V ) /\ ( ( 1st ` Y ) = ( ( 2nd ` Y ) ` G ) /\ ( 2nd ` Y ) e. E ) ) ) )

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
    cY
    cQ
    cI
    cfv
    wcel
    cY
    cvv
    cvv
    cxp
    wcel
    #
    cY
    c1st
    cfv
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
    cY
    c2nd
    cfv
    #
    cfv
    #
    wceq
    #
    @3
    cE
    wcel
    #
    wa
    #
    wa
    @0
    @1
    cG
    @3
    cfv
    #
    wceq
    #
    @6
    wa
    #
    wa
    cA
    cP
    cQ
    cT
    vg
    cE
    cH
    cI
    cK
    c.le
    cV
    cW
    cY
    dicval.l
    dicval.a
    dicval.h
    dicval.p
    dicval.t
    dicval.e
    dicval.i
    dicelvalN
    @10
    @7
    @0
    @9
    @5
    @6
    @8
    @4
    @1
    cG
    @2
    @3
    dicval2.g
    fveq2i
    eqeq2i
    anbi1i
    anbi2i
    syl6bbr
end

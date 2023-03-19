include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "cop.mm"
include "cfv.mm"
include "cv.mm"
include "wceq.mm"
include "crio.mm"
include "dicopelval.mm"
include "fveq2i.mm"
include "eqeq2i.mm"
include "anbi1i.mm"
include "syl6bbr.mm"

theorem dicopelval2
  let cA: class A
  let cP: class P
  let cQ: class Q
  let cS: class S
  let cT: class T
  let vg: setvar g
  let cE: class E
  let cF: class F
  let cG: class G
  let cH: class H
  let cI: class I
  let cK: class K
  let c.le: class .<_
  let cV: class V
  let cW: class W
  let vk: setvar k
  let vr: setvar r
  let vw: setvar w
  let vf: setvar f
  let vq: setvar q
  let vs: setvar s
  let cY: class Y
  assume dicval.l: |- .<_ = ( le ` K )
  assume dicval.a: |- A = ( Atoms ` K )
  assume dicval.h: |- H = ( LHyp ` K )
  assume dicval.p: |- P = ( ( oc ` K ) ` W )
  assume dicval.t: |- T = ( ( LTrn ` K ) ` W )
  assume dicval.e: |- E = ( ( TEndo ` K ) ` W )
  assume dicval.i: |- I = ( ( DIsoC ` K ) ` W )
  assume dicval2.g: |- G = ( iota_ g e. T ( g ` P ) = Q )
  assume dicelval2.f: |- F e. _V
  assume dicelval2.s: |- S e. _V

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
  assert |- ( ( ( K e. V /\ W e. H ) /\ ( Q e. A /\ -. Q .<_ W ) ) -> ( <. F , S >. e. ( I ` Q ) <-> ( F = ( S ` G ) /\ S e. E ) ) )

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
    cF
    cS
    cop
    cQ
    cI
    cfv
    wcel
    cF
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
    cF
    cG
    cS
    cfv
    #
    wceq
    #
    @3
    wa
    cA
    cP
    cQ
    cS
    cT
    vg
    cE
    cF
    cH
    cI
    cK
    c.le
    cV
    cW
    dicval.l
    dicval.a
    dicval.h
    dicval.p
    dicval.t
    dicval.e
    dicval.i
    dicelval2.f
    dicelval2.s
    dicopelval
    @5
    @2
    @3
    @4
    @1
    cF
    cG
    @0
    cS
    dicval2.g
    fveq2i
    eqeq2i
    anbi1i
    syl6bbr
end

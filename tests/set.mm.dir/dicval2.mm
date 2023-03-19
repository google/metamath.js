include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "cfv.mm"
include "cv.mm"
include "wceq.mm"
include "crio.mm"
include "copab.mm"
include "dicval.mm"
include "fveq2i.mm"
include "eqeq2i.mm"
include "anbi1i.mm"
include "opabbii.mm"
include "syl6eqr.mm"

theorem dicval2
  let cA: class A
  let cP: class P
  let cQ: class Q
  let cT: class T
  let vf: setvar f
  let vg: setvar g
  let cE: class E
  let cG: class G
  let cH: class H
  let cI: class I
  let cK: class K
  let c.le: class .<_
  let cV: class V
  let cW: class W
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
  assume dicval2.g: |- G = ( iota_ g e. T ( g ` P ) = Q )

  disjoint f g
  disjoint f s
  disjoint K f
  disjoint g s
  disjoint K g
  disjoint K s
  disjoint T g
  disjoint W f
  disjoint W g
  disjoint W s
  disjoint E f
  disjoint E s
  disjoint P f
  disjoint Q f
  disjoint Q g
  disjoint Q s
  disjoint T f
  disjoint .<_ k
  disjoint k r
  disjoint A k
  disjoint A r
  disjoint k w
  disjoint H k
  disjoint H w
  disjoint f k
  disjoint f q
  disjoint f r
  disjoint f w
  disjoint g k
  disjoint g q
  disjoint g r
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
  disjoint K w
  disjoint .<_ q
  disjoint .<_ w
  disjoint A q
  disjoint A w
  disjoint E w
  disjoint P w
  disjoint T w
  disjoint W q
  disjoint W r
  disjoint W w
  disjoint .<_ r
  disjoint E q
  disjoint P q
  disjoint Q q
  disjoint Q r
  disjoint T q
  assert |- ( ( ( K e. V /\ W e. H ) /\ ( Q e. A /\ -. Q .<_ W ) ) -> ( I ` Q ) = { <. f , s >. | ( f = ( s ` G ) /\ s e. E ) } )

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
    cQ
    cI
    cfv
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
    @2
    cE
    wcel
    #
    wa
    #
    vf
    vs
    copab
    @0
    cG
    @2
    cfv
    #
    wceq
    #
    @5
    wa
    #
    vf
    vs
    copab
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
    @9
    @6
    vf
    vs
    @8
    @4
    @5
    @7
    @3
    @0
    cG
    @1
    @2
    dicval2.g
    fveq2i
    eqeq2i
    anbi1i
    opabbii
    syl6eqr
end

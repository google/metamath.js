include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "cfv.mm"
include "cv.mm"
include "wceq.mm"
include "copab.mm"
include "cop.mm"
include "wrex.mm"
include "dicval2.mm"
include "eleq2d.mm"
include "wex.mm"
include "excom.mm"
include "an12.mm"
include "exbii.mm"
include "fvex.mm"
include "opeq1.mm"
include "eqeq2d.mm"
include "anbi1d.mm"
include "ceqsexv.mm"
include "ancom.mm"
include "3bitri.mm"
include "bitri.mm"
include "elopab.mm"
include "df-rex.mm"
include "3bitr4i.mm"
include "syl6bb.mm"

theorem dicelval3
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
  let vs: setvar s
  let vk: setvar k
  let vr: setvar r
  let vw: setvar w
  let vf: setvar f
  let vq: setvar q
  assume dicval.l: |- .<_ = ( le ` K )
  assume dicval.a: |- A = ( Atoms ` K )
  assume dicval.h: |- H = ( LHyp ` K )
  assume dicval.p: |- P = ( ( oc ` K ) ` W )
  assume dicval.t: |- T = ( ( LTrn ` K ) ` W )
  assume dicval.e: |- E = ( ( TEndo ` K ) ` W )
  assume dicval.i: |- I = ( ( DIsoC ` K ) ` W )
  assume dicval2.g: |- G = ( iota_ g e. T ( g ` P ) = Q )

  disjoint g s
  disjoint K g
  disjoint K s
  disjoint T g
  disjoint W g
  disjoint W s
  disjoint E s
  disjoint Q g
  disjoint Q s
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
  disjoint W f
  disjoint W q
  disjoint W r
  disjoint W w
  disjoint .<_ r
  disjoint E f
  disjoint E q
  disjoint P f
  disjoint P q
  disjoint Q f
  disjoint Q q
  disjoint Q r
  disjoint T f
  disjoint T q
  disjoint G f
  disjoint Y f
  assert |- ( ( ( K e. V /\ W e. H ) /\ ( Q e. A /\ -. Q .<_ W ) ) -> ( Y e. ( I ` Q ) <-> E. s e. E Y = <. ( s ` G ) , s >. ) )

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
    cG
    vs
    cv
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
    vf
    vs
    copab
    #
    wcel
    #
    cY
    @4
    @3
    cop
    #
    wceq
    #
    vs
    cE
    wrex
    #
    @0
    @1
    @8
    cY
    cA
    cP
    cQ
    cT
    vf
    vg
    cE
    cG
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
    dicval2.g
    dicval2
    eleq2d
    cY
    @2
    @3
    cop
    #
    wceq
    #
    @7
    wa
    #
    vs
    wex
    vf
    wex
    #
    @6
    @11
    wa
    #
    vs
    wex
    #
    @9
    @12
    @16
    @15
    vf
    wex
    #
    vs
    wex
    @18
    @15
    vf
    vs
    excom
    @19
    @17
    vs
    @19
    @5
    @14
    @6
    wa
    #
    wa
    #
    vf
    wex
    @11
    @6
    wa
    #
    @17
    @15
    @21
    vf
    @14
    @5
    @6
    an12
    exbii
    @20
    @22
    vf
    @4
    cG
    @3
    fvex
    @5
    @14
    @11
    @6
    @5
    @13
    @10
    cY
    @2
    @4
    @3
    opeq1
    eqeq2d
    anbi1d
    ceqsexv
    @11
    @6
    ancom
    3bitri
    exbii
    bitri
    @7
    vf
    vs
    cY
    elopab
    @11
    vs
    cE
    df-rex
    3bitr4i
    syl6bb
end

include "wcel.mm"
include "wf.mm"
include "cv.mm"
include "ccom.mm"
include "cfv.mm"
include "wceq.mm"
include "wral.mm"
include "wbr.mm"
include "3expb.mm"
include "ralrimivva.mm"
include "ralrimiva.mm"
include "wa.mm"
include "w3a.mm"
include "wb.mm"
include "istendo.mm"
include "syl.mm"
include "mpbir3and.mm"

theorem istendod
  let wph: wff ph
  let cR: class R
  let cS: class S
  let cT: class T
  let vf: setvar f
  let vg: setvar g
  let cE: class E
  let cH: class H
  let cK: class K
  let c.le: class .<_
  let cV: class V
  let cW: class W
  let vk: setvar k
  let vw: setvar w
  let vs: setvar s
  let cF: class F
  assume tendoset.l: |- .<_ = ( le ` K )
  assume tendoset.h: |- H = ( LHyp ` K )
  assume tendoset.t: |- T = ( ( LTrn ` K ) ` W )
  assume tendoset.r: |- R = ( ( trL ` K ) ` W )
  assume tendoset.e: |- E = ( ( TEndo ` K ) ` W )
  assume istendod.1: |- ( ph -> ( K e. V /\ W e. H ) )
  assume istendod.2: |- ( ph -> S : T --> T )
  assume istendod.3: |- ( ( ph /\ f e. T /\ g e. T ) -> ( S ` ( f o. g ) ) = ( ( S ` f ) o. ( S ` g ) ) )
  assume istendod.4: |- ( ( ph /\ f e. T ) -> ( R ` ( S ` f ) ) .<_ ( R ` f ) )

  disjoint f g
  disjoint K f
  disjoint K g
  disjoint T f
  disjoint T g
  disjoint W f
  disjoint W g
  disjoint S f
  disjoint S g
  disjoint .<_ f
  disjoint R f
  disjoint f ph
  disjoint g ph
  disjoint .<_ k
  disjoint k w
  disjoint H k
  disjoint H w
  disjoint k s
  disjoint s w
  disjoint f s
  disjoint g s
  disjoint K s
  disjoint f k
  disjoint g k
  disjoint K k
  disjoint f w
  disjoint g w
  disjoint K w
  disjoint R k
  disjoint T k
  disjoint .<_ w
  disjoint R w
  disjoint T s
  disjoint T w
  disjoint W s
  disjoint W w
  disjoint R s
  disjoint S s
  disjoint .<_ s
  disjoint F f
  assert |- ( ph -> S e. E )

  proof
    wph
    cS
    cE
    wcel
    #
    cT
    cT
    cS
    wf
    #
    vf
    cv
    #
    vg
    cv
    #
    ccom
    cS
    cfv
    @2
    cS
    cfv
    #
    @3
    cS
    cfv
    ccom
    wceq
    #
    vg
    cT
    wral
    vf
    cT
    wral
    #
    @4
    cR
    cfv
    @2
    cR
    cfv
    c.le
    wbr
    #
    vf
    cT
    wral
    #
    istendod.2
    wph
    @5
    vf
    vg
    cT
    cT
    wph
    @2
    cT
    wcel
    @3
    cT
    wcel
    @5
    istendod.3
    3expb
    ralrimivva
    wph
    @7
    vf
    cT
    istendod.4
    ralrimiva
    wph
    cK
    cV
    wcel
    cW
    cH
    wcel
    wa
    @0
    @1
    @6
    @8
    w3a
    wb
    istendod.1
    cR
    cS
    cT
    vf
    vg
    cE
    cH
    cK
    c.le
    cV
    cW
    tendoset.l
    tendoset.h
    tendoset.t
    tendoset.r
    tendoset.e
    istendo
    syl
    mpbir3and
end

include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "wf.mm"
include "ccom.mm"
include "cfv.mm"
include "wceq.mm"
include "wral.mm"
include "wbr.mm"
include "w3a.mm"
include "cab.mm"
include "tendoset.mm"
include "eleq2d.mm"
include "cvv.mm"
include "cltrn.mm"
include "fvex.mm"
include "eqeltri.mm"
include "fex.mm"
include "mpan2.mm"
include "3ad2ant1.mm"
include "feq1.mm"
include "fveq1.mm"
include "coeq12d.mm"
include "eqeq12d.mm"
include "2ralbidv.mm"
include "fveq2d.mm"
include "breq1d.mm"
include "ralbidv.mm"
include "3anbi123d.mm"
include "elab3.mm"
include "syl6bb.mm"

theorem istendo
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
  assume tendoset.l: |- .<_ = ( le ` K )
  assume tendoset.h: |- H = ( LHyp ` K )
  assume tendoset.t: |- T = ( ( LTrn ` K ) ` W )
  assume tendoset.r: |- R = ( ( trL ` K ) ` W )
  assume tendoset.e: |- E = ( ( TEndo ` K ) ` W )

  disjoint f g
  disjoint K f
  disjoint K g
  disjoint T f
  disjoint T g
  disjoint W f
  disjoint W g
  disjoint S f
  disjoint S g
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
  assert |- ( ( K e. V /\ W e. H ) -> ( S e. E <-> ( S : T --> T /\ A. f e. T A. g e. T ( S ` ( f o. g ) ) = ( ( S ` f ) o. ( S ` g ) ) /\ A. f e. T ( R ` ( S ` f ) ) .<_ ( R ` f ) ) ) )

  proof
    cK
    cV
    wcel
    cW
    cH
    wcel
    wa
    #
    cS
    cE
    wcel
    cS
    cT
    cT
    vs
    cv
    #
    wf
    #
    vf
    cv
    #
    vg
    cv
    #
    ccom
    #
    @1
    cfv
    #
    @3
    @1
    cfv
    #
    @4
    @1
    cfv
    #
    ccom
    #
    wceq
    #
    vg
    cT
    wral
    vf
    cT
    wral
    #
    @7
    cR
    cfv
    #
    @3
    cR
    cfv
    #
    c.le
    wbr
    #
    vf
    cT
    wral
    #
    w3a
    #
    vs
    cab
    #
    wcel
    cT
    cT
    cS
    wf
    #
    @5
    cS
    cfv
    #
    @3
    cS
    cfv
    #
    @4
    cS
    cfv
    #
    ccom
    #
    wceq
    #
    vg
    cT
    wral
    vf
    cT
    wral
    #
    @20
    cR
    cfv
    #
    @13
    c.le
    wbr
    #
    vf
    cT
    wral
    #
    w3a
    #
    @0
    cE
    @17
    cS
    cR
    cT
    vf
    vg
    cE
    cH
    cK
    c.le
    cV
    cW
    vs
    tendoset.l
    tendoset.h
    tendoset.t
    tendoset.r
    tendoset.e
    tendoset
    eleq2d
    @16
    @28
    vs
    cS
    @18
    @24
    cS
    cvv
    wcel
    #
    @27
    @18
    cT
    cvv
    wcel
    @29
    cT
    cW
    cK
    cltrn
    cfv
    #
    cfv
    cvv
    tendoset.t
    cW
    @30
    fvex
    eqeltri
    cT
    cT
    cvv
    cS
    fex
    mpan2
    3ad2ant1
    @1
    cS
    wceq
    #
    @2
    @18
    @11
    @24
    @15
    @27
    cT
    cT
    @1
    cS
    feq1
    @31
    @10
    @23
    vf
    vg
    cT
    cT
    @31
    @6
    @19
    @9
    @22
    @5
    @1
    cS
    fveq1
    @31
    @7
    @20
    @8
    @21
    @3
    @1
    cS
    fveq1
    #
    @4
    @1
    cS
    fveq1
    coeq12d
    eqeq12d
    2ralbidv
    @31
    @14
    @26
    vf
    cT
    @31
    @12
    @25
    @13
    c.le
    @31
    @7
    @20
    cR
    @32
    fveq2d
    breq1d
    ralbidv
    3anbi123d
    elab3
    syl6bb
end

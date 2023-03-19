include "wcel.mm"
include "wa.mm"
include "ctendo.mm"
include "cfv.mm"
include "cv.mm"
include "wf.mm"
include "ccom.mm"
include "wceq.mm"
include "wral.mm"
include "wbr.mm"
include "w3a.mm"
include "cab.mm"
include "cltrn.mm"
include "ctrl.mm"
include "cmpt.mm"
include "tendofset.mm"
include "fveq1d.mm"
include "fveq2.mm"
include "feq23d.mm"
include "raleqdv.mm"
include "raleqbidv.mm"
include "syl6eqr.mm"
include "breq12d.mm"
include "3anbi123d.mm"
include "abbidv.mm"
include "eqid.mm"
include "cmap.mm"
include "co.mm"
include "cvv.mm"
include "fvex.mm"
include "mapval.mm"
include "ovex.mm"
include "eqeltrri.mm"
include "simp1.mm"
include "ss2abi.mm"
include "ssexi.mm"
include "fvmpt.mm"
include "feq23i.mm"
include "raleqi.mm"
include "raleqbii.mm"
include "3anbi123i.mm"
include "abbii.mm"
include "sylan9eq.mm"
include "syl5eq.mm"

theorem tendoset
  let cR: class R
  let cT: class T
  let vf: setvar f
  let vg: setvar g
  let cE: class E
  let cH: class H
  let cK: class K
  let c.le: class .<_
  let cV: class V
  let cW: class W
  let vs: setvar s
  let vk: setvar k
  let vw: setvar w
  assume tendoset.l: |- .<_ = ( le ` K )
  assume tendoset.h: |- H = ( LHyp ` K )
  assume tendoset.t: |- T = ( ( LTrn ` K ) ` W )
  assume tendoset.r: |- R = ( ( trL ` K ) ` W )
  assume tendoset.e: |- E = ( ( TEndo ` K ) ` W )

  disjoint f s
  disjoint g s
  disjoint K s
  disjoint f g
  disjoint K f
  disjoint K g
  disjoint T f
  disjoint T g
  disjoint T s
  disjoint W s
  disjoint W f
  disjoint W g
  disjoint .<_ k
  disjoint k w
  disjoint H k
  disjoint H w
  disjoint k s
  disjoint s w
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
  disjoint T w
  disjoint W w
  assert |- ( ( K e. V /\ W e. H ) -> E = { s | ( s : T --> T /\ A. f e. T A. g e. T ( s ` ( f o. g ) ) = ( ( s ` f ) o. ( s ` g ) ) /\ A. f e. T ( R ` ( s ` f ) ) .<_ ( R ` f ) ) } )

  proof
    cK
    cV
    wcel
    #
    cW
    cH
    wcel
    #
    wa
    cE
    cW
    cK
    ctendo
    cfv
    #
    cfv
    #
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
    @4
    cfv
    @6
    @4
    cfv
    #
    @7
    @4
    cfv
    ccom
    wceq
    #
    vg
    cT
    wral
    #
    vf
    cT
    wral
    #
    @8
    cR
    cfv
    #
    @6
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
    tendoset.e
    @0
    @1
    @3
    cW
    vw
    cH
    vw
    cv
    #
    cK
    cltrn
    cfv
    #
    cfv
    #
    @20
    @4
    wf
    #
    @9
    vg
    @20
    wral
    #
    vf
    @20
    wral
    #
    @8
    @18
    cK
    ctrl
    cfv
    #
    cfv
    #
    cfv
    #
    @6
    @25
    cfv
    #
    c.le
    wbr
    #
    vf
    @20
    wral
    #
    w3a
    #
    vs
    cab
    #
    cmpt
    #
    cfv
    #
    @17
    @0
    cW
    @2
    @32
    vw
    vf
    vg
    cH
    cK
    c.le
    cV
    vs
    tendoset.l
    tendoset.h
    tendofset
    fveq1d
    @1
    @33
    cW
    @19
    cfv
    #
    @34
    @4
    wf
    #
    @9
    vg
    @34
    wral
    #
    vf
    @34
    wral
    #
    @14
    vf
    @34
    wral
    #
    w3a
    #
    vs
    cab
    #
    @17
    vw
    cW
    @31
    @40
    cH
    @32
    @18
    cW
    wceq
    #
    @30
    @39
    vs
    @41
    @21
    @35
    @23
    @37
    @29
    @38
    @41
    @20
    @20
    @34
    @34
    @4
    @18
    cW
    @19
    fveq2
    #
    @42
    feq23d
    @41
    @22
    @36
    vf
    @20
    @34
    @42
    @41
    @9
    vg
    @20
    @34
    @42
    raleqdv
    raleqbidv
    @41
    @28
    @14
    vf
    @20
    @34
    @42
    @41
    @26
    @12
    @27
    @13
    c.le
    @41
    @8
    @25
    cR
    @41
    @25
    cW
    @24
    cfv
    cR
    @18
    cW
    @24
    fveq2
    tendoset.r
    syl6eqr
    #
    fveq1d
    @41
    @6
    @25
    cR
    @43
    fveq1d
    breq12d
    raleqbidv
    3anbi123d
    abbidv
    @32
    eqid
    @40
    @35
    vs
    cab
    #
    @34
    @34
    cmap
    co
    @44
    cvv
    @34
    @34
    vs
    cW
    @19
    fvex
    #
    @45
    mapval
    @34
    @34
    cmap
    ovex
    eqeltrri
    @39
    @35
    vs
    @35
    @37
    @38
    simp1
    ss2abi
    ssexi
    fvmpt
    @16
    @39
    vs
    @5
    @35
    @11
    @37
    @15
    @38
    cT
    cT
    @34
    @34
    @4
    tendoset.t
    tendoset.t
    feq23i
    @10
    @36
    vf
    cT
    @34
    tendoset.t
    @9
    vg
    cT
    @34
    tendoset.t
    raleqi
    raleqbii
    @14
    vf
    cT
    @34
    tendoset.t
    raleqi
    3anbi123i
    abbii
    syl6eqr
    sylan9eq
    syl5eq
end

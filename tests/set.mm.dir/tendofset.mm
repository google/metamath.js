include "wcel.mm"
include "cvv.mm"
include "ctendo.mm"
include "cfv.mm"
include "cv.mm"
include "cltrn.mm"
include "wf.mm"
include "ccom.mm"
include "wceq.mm"
include "wral.mm"
include "ctrl.mm"
include "wbr.mm"
include "w3a.mm"
include "cab.mm"
include "cmpt.mm"
include "elex.mm"
include "clh.mm"
include "cple.mm"
include "fveq2.mm"
include "syl6eqr.mm"
include "fveq1d.mm"
include "feq23d.mm"
include "raleqdv.mm"
include "raleqbidv.mm"
include "breq123d.mm"
include "3anbi123d.mm"
include "abbidv.mm"
include "mpteq12dv.mm"
include "df-tendo.mm"
include "fvex.mm"
include "eqeltri.mm"
include "mptex.mm"
include "fvmpt.mm"
include "syl.mm"

theorem tendofset
  let vw: setvar w
  let vf: setvar f
  let vg: setvar g
  let cH: class H
  let cK: class K
  let c.le: class .<_
  let cV: class V
  let vs: setvar s
  let vk: setvar k
  let cR: class R
  let cT: class T
  assume tendoset.l: |- .<_ = ( le ` K )
  assume tendoset.h: |- H = ( LHyp ` K )

  disjoint H w
  disjoint s w
  disjoint f s
  disjoint g s
  disjoint K s
  disjoint f w
  disjoint g w
  disjoint K w
  disjoint f g
  disjoint K f
  disjoint K g
  disjoint .<_ k
  disjoint k w
  disjoint H k
  disjoint k s
  disjoint f k
  disjoint g k
  disjoint K k
  disjoint R k
  disjoint T k
  disjoint T f
  disjoint T g
  assert |- ( K e. V -> ( TEndo ` K ) = ( w e. H |-> { s | ( s : ( ( LTrn ` K ) ` w ) --> ( ( LTrn ` K ) ` w ) /\ A. f e. ( ( LTrn ` K ) ` w ) A. g e. ( ( LTrn ` K ) ` w ) ( s ` ( f o. g ) ) = ( ( s ` f ) o. ( s ` g ) ) /\ A. f e. ( ( LTrn ` K ) ` w ) ( ( ( trL ` K ) ` w ) ` ( s ` f ) ) .<_ ( ( ( trL ` K ) ` w ) ` f ) ) } ) )

  proof
    cK
    cV
    wcel
    cK
    cvv
    wcel
    cK
    ctendo
    cfv
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
    @2
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
    @3
    cfv
    @5
    @3
    cfv
    #
    @6
    @3
    cfv
    ccom
    wceq
    #
    vg
    @2
    wral
    #
    vf
    @2
    wral
    #
    @7
    @0
    cK
    ctrl
    cfv
    #
    cfv
    #
    cfv
    #
    @5
    @12
    cfv
    #
    c.le
    wbr
    #
    vf
    @2
    wral
    #
    w3a
    #
    vs
    cab
    #
    cmpt
    #
    wceq
    cK
    cV
    elex
    vk
    cK
    vw
    vk
    cv
    #
    clh
    cfv
    #
    @0
    @20
    cltrn
    cfv
    #
    cfv
    #
    @23
    @3
    wf
    #
    @8
    vg
    @23
    wral
    #
    vf
    @23
    wral
    #
    @7
    @0
    @20
    ctrl
    cfv
    #
    cfv
    #
    cfv
    #
    @5
    @28
    cfv
    #
    @20
    cple
    cfv
    #
    wbr
    #
    vf
    @23
    wral
    #
    w3a
    #
    vs
    cab
    #
    cmpt
    @19
    cvv
    ctendo
    @20
    cK
    wceq
    #
    vw
    @21
    @35
    cH
    @18
    @36
    @21
    cK
    clh
    cfv
    #
    cH
    @20
    cK
    clh
    fveq2
    tendoset.h
    syl6eqr
    @36
    @34
    @17
    vs
    @36
    @24
    @4
    @26
    @10
    @33
    @16
    @36
    @23
    @23
    @2
    @2
    @3
    @36
    @0
    @22
    @1
    @20
    cK
    cltrn
    fveq2
    fveq1d
    #
    @38
    feq23d
    @36
    @25
    @9
    vf
    @23
    @2
    @38
    @36
    @8
    vg
    @23
    @2
    @38
    raleqdv
    raleqbidv
    @36
    @32
    @15
    vf
    @23
    @2
    @38
    @36
    @29
    @13
    @30
    @14
    @31
    c.le
    @36
    @7
    @28
    @12
    @36
    @0
    @27
    @11
    @20
    cK
    ctrl
    fveq2
    fveq1d
    #
    fveq1d
    @36
    @31
    cK
    cple
    cfv
    c.le
    @20
    cK
    cple
    fveq2
    tendoset.l
    syl6eqr
    @36
    @5
    @28
    @12
    @39
    fveq1d
    breq123d
    raleqbidv
    3anbi123d
    abbidv
    mpteq12dv
    vf
    vg
    vw
    vs
    vk
    df-tendo
    vw
    cH
    @18
    cH
    @37
    cvv
    tendoset.h
    cK
    clh
    fvex
    eqeltri
    mptex
    fvmpt
    syl
end

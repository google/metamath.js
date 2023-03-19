include "wcel.mm"
include "cnx.mm"
include "cbs.mm"
include "cfv.mm"
include "cv.mm"
include "cltrn.mm"
include "ctendo.mm"
include "cxp.mm"
include "cop.mm"
include "cplusg.mm"
include "c1st.mm"
include "ccom.mm"
include "c2nd.mm"
include "cmpt.mm"
include "cmpt2.mm"
include "csca.mm"
include "cedring.mm"
include "ctp.mm"
include "cvsca.mm"
include "csn.mm"
include "cun.mm"
include "cdvh.mm"
include "dvhfset.mm"
include "fveq1d.mm"
include "syl5eq.mm"
include "wceq.mm"
include "fveq2.mm"
include "syl6eqr.mm"
include "xpeq12d.mm"
include "opeq2d.mm"
include "mpteq1d.mm"
include "mpt2eq123dv.mm"
include "tpeq123d.mm"
include "eqidd.mm"
include "sneqd.mm"
include "uneq12d.mm"
include "eqid.mm"
include "tpex.mm"
include "snex.mm"
include "unex.mm"
include "fvmpt.mm"
include "sylan9eq.mm"

theorem dvhset
  let cD: class D
  let cT: class T
  let cU: class U
  let vf: setvar f
  let vg: setvar g
  let vh: setvar h
  let cE: class E
  let cH: class H
  let cK: class K
  let cW: class W
  let cX: class X
  let vs: setvar s
  let vw: setvar w
  let vk: setvar k
  assume dvhset.h: |- H = ( LHyp ` K )
  assume dvhset.t: |- T = ( ( LTrn ` K ) ` W )
  assume dvhset.e: |- E = ( ( TEndo ` K ) ` W )
  assume dvhset.d: |- D = ( ( EDRing ` K ) ` W )
  assume dvhset.u: |- U = ( ( DVecH ` K ) ` W )

  disjoint f g
  disjoint H f
  disjoint H g
  disjoint f h
  disjoint f s
  disjoint K f
  disjoint g h
  disjoint g s
  disjoint K g
  disjoint h s
  disjoint K h
  disjoint K s
  disjoint T h
  disjoint W f
  disjoint W g
  disjoint W h
  disjoint W s
  disjoint X f
  disjoint X g
  disjoint D w
  disjoint E w
  disjoint f k
  disjoint f w
  disjoint g k
  disjoint g w
  disjoint k w
  disjoint H k
  disjoint H w
  disjoint h k
  disjoint h w
  disjoint k s
  disjoint K k
  disjoint s w
  disjoint K w
  disjoint T w
  disjoint W w
  assert |- ( ( K e. X /\ W e. H ) -> U = ( { <. ( Base ` ndx ) , ( T X. E ) >. , <. ( +g ` ndx ) , ( f e. ( T X. E ) , g e. ( T X. E ) |-> <. ( ( 1st ` f ) o. ( 1st ` g ) ) , ( h e. T |-> ( ( ( 2nd ` f ) ` h ) o. ( ( 2nd ` g ) ` h ) ) ) >. ) >. , <. ( Scalar ` ndx ) , D >. } u. { <. ( .s ` ndx ) , ( s e. E , f e. ( T X. E ) |-> <. ( s ` ( 1st ` f ) ) , ( s o. ( 2nd ` f ) ) >. ) >. } ) )

  proof
    cK
    cX
    wcel
    #
    cW
    cH
    wcel
    cU
    cW
    vw
    cH
    cnx
    cbs
    cfv
    #
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
    cK
    ctendo
    cfv
    #
    cfv
    #
    cxp
    #
    cop
    #
    cnx
    cplusg
    cfv
    #
    vf
    vg
    @7
    @7
    vf
    cv
    #
    c1st
    cfv
    #
    vg
    cv
    #
    c1st
    cfv
    ccom
    #
    vh
    @4
    vh
    cv
    #
    @10
    c2nd
    cfv
    #
    cfv
    @14
    @12
    c2nd
    cfv
    cfv
    ccom
    #
    cmpt
    #
    cop
    #
    cmpt2
    #
    cop
    #
    cnx
    csca
    cfv
    #
    @2
    cK
    cedring
    cfv
    #
    cfv
    #
    cop
    #
    ctp
    #
    cnx
    cvsca
    cfv
    #
    vs
    vf
    @6
    @7
    @11
    vs
    cv
    #
    cfv
    @27
    @15
    ccom
    cop
    #
    cmpt2
    #
    cop
    #
    csn
    #
    cun
    #
    cmpt
    #
    cfv
    #
    @1
    cT
    cE
    cxp
    #
    cop
    #
    @9
    vf
    vg
    @35
    @35
    @13
    vh
    cT
    @16
    cmpt
    #
    cop
    #
    cmpt2
    #
    cop
    #
    @21
    cD
    cop
    #
    ctp
    #
    @26
    vs
    vf
    cE
    @35
    @28
    cmpt2
    #
    cop
    #
    csn
    #
    cun
    #
    @0
    cU
    cW
    cK
    cdvh
    cfv
    #
    cfv
    @34
    dvhset.u
    @0
    cW
    @47
    @33
    vw
    vf
    vg
    vh
    cH
    cK
    cX
    vs
    dvhset.h
    dvhfset
    fveq1d
    syl5eq
    vw
    cW
    @32
    @46
    cH
    @33
    @2
    cW
    wceq
    #
    @25
    @42
    @31
    @45
    @48
    @8
    @36
    @20
    @40
    @24
    @41
    @48
    @7
    @35
    @1
    @48
    @4
    cT
    @6
    cE
    @48
    @4
    cW
    @3
    cfv
    cT
    @2
    cW
    @3
    fveq2
    dvhset.t
    syl6eqr
    #
    @48
    @6
    cW
    @5
    cfv
    cE
    @2
    cW
    @5
    fveq2
    dvhset.e
    syl6eqr
    #
    xpeq12d
    #
    opeq2d
    @48
    @19
    @39
    @9
    @48
    vf
    vg
    @7
    @7
    @18
    @35
    @35
    @38
    @51
    @51
    @48
    @17
    @37
    @13
    @48
    vh
    @4
    cT
    @16
    @49
    mpteq1d
    opeq2d
    mpt2eq123dv
    opeq2d
    @48
    @23
    cD
    @21
    @48
    @23
    cW
    @22
    cfv
    cD
    @2
    cW
    @22
    fveq2
    dvhset.d
    syl6eqr
    opeq2d
    tpeq123d
    @48
    @30
    @44
    @48
    @29
    @43
    @26
    @48
    vs
    vf
    @6
    @7
    @28
    cE
    @35
    @28
    @50
    @51
    @48
    @28
    eqidd
    mpt2eq123dv
    opeq2d
    sneqd
    uneq12d
    @33
    eqid
    @42
    @45
    @36
    @40
    @41
    tpex
    @44
    snex
    unex
    fvmpt
    sylan9eq
end

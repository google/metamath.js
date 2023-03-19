include "wcel.mm"
include "cvv.mm"
include "cdvh.mm"
include "cfv.mm"
include "cnx.mm"
include "cbs.mm"
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
include "wceq.mm"
include "elex.mm"
include "clh.mm"
include "fveq2.mm"
include "syl6eqr.mm"
include "fveq1d.mm"
include "xpeq12d.mm"
include "opeq2d.mm"
include "mpteq1d.mm"
include "mpt2eq123dv.mm"
include "tpeq123d.mm"
include "eqidd.mm"
include "sneqd.mm"
include "uneq12d.mm"
include "mpteq12dv.mm"
include "df-dvech.mm"
include "fvex.mm"
include "eqeltri.mm"
include "mptex.mm"
include "fvmpt.mm"
include "syl.mm"

theorem dvhfset
  let vw: setvar w
  let vf: setvar f
  let vg: setvar g
  let vh: setvar h
  let cH: class H
  let cK: class K
  let cV: class V
  let vs: setvar s
  let cD: class D
  let cE: class E
  let vk: setvar k
  let cT: class T
  let cW: class W
  let cX: class X
  assume dvhset.h: |- H = ( LHyp ` K )

  disjoint f g
  disjoint f w
  disjoint H f
  disjoint g w
  disjoint H g
  disjoint H w
  disjoint f h
  disjoint f s
  disjoint K f
  disjoint g h
  disjoint g s
  disjoint K g
  disjoint h s
  disjoint h w
  disjoint K h
  disjoint s w
  disjoint K s
  disjoint K w
  disjoint D w
  disjoint E w
  disjoint f k
  disjoint g k
  disjoint k w
  disjoint H k
  disjoint h k
  disjoint k s
  disjoint K k
  disjoint T h
  disjoint T w
  disjoint W f
  disjoint W g
  disjoint W h
  disjoint W s
  disjoint W w
  disjoint X f
  disjoint X g
  assert |- ( K e. V -> ( DVecH ` K ) = ( w e. H |-> ( { <. ( Base ` ndx ) , ( ( ( LTrn ` K ) ` w ) X. ( ( TEndo ` K ) ` w ) ) >. , <. ( +g ` ndx ) , ( f e. ( ( ( LTrn ` K ) ` w ) X. ( ( TEndo ` K ) ` w ) ) , g e. ( ( ( LTrn ` K ) ` w ) X. ( ( TEndo ` K ) ` w ) ) |-> <. ( ( 1st ` f ) o. ( 1st ` g ) ) , ( h e. ( ( LTrn ` K ) ` w ) |-> ( ( ( 2nd ` f ) ` h ) o. ( ( 2nd ` g ) ` h ) ) ) >. ) >. , <. ( Scalar ` ndx ) , ( ( EDRing ` K ) ` w ) >. } u. { <. ( .s ` ndx ) , ( s e. ( ( TEndo ` K ) ` w ) , f e. ( ( ( LTrn ` K ) ` w ) X. ( ( TEndo ` K ) ` w ) ) |-> <. ( s ` ( 1st ` f ) ) , ( s o. ( 2nd ` f ) ) >. ) >. } ) ) )

  proof
    cK
    cV
    wcel
    cK
    cvv
    wcel
    cK
    cdvh
    cfv
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
    @1
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
    @6
    @6
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
    @3
    vh
    cv
    #
    @9
    c2nd
    cfv
    #
    cfv
    @13
    @11
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
    @1
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
    @5
    @6
    @10
    vs
    cv
    #
    cfv
    @26
    @14
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
    @1
    @33
    cltrn
    cfv
    #
    cfv
    #
    @1
    @33
    ctendo
    cfv
    #
    cfv
    #
    cxp
    #
    cop
    #
    @8
    vf
    vg
    @39
    @39
    @12
    vh
    @36
    @15
    cmpt
    #
    cop
    #
    cmpt2
    #
    cop
    #
    @20
    @1
    @33
    cedring
    cfv
    #
    cfv
    #
    cop
    #
    ctp
    #
    @25
    vs
    vf
    @38
    @39
    @27
    cmpt2
    #
    cop
    #
    csn
    #
    cun
    #
    cmpt
    @32
    cvv
    cdvh
    @33
    cK
    wceq
    #
    vw
    @34
    @52
    cH
    @31
    @53
    @34
    cK
    clh
    cfv
    #
    cH
    @33
    cK
    clh
    fveq2
    dvhset.h
    syl6eqr
    @53
    @48
    @24
    @51
    @30
    @53
    @40
    @7
    @44
    @19
    @47
    @23
    @53
    @39
    @6
    @0
    @53
    @36
    @3
    @38
    @5
    @53
    @1
    @35
    @2
    @33
    cK
    cltrn
    fveq2
    fveq1d
    #
    @53
    @1
    @37
    @4
    @33
    cK
    ctendo
    fveq2
    fveq1d
    #
    xpeq12d
    #
    opeq2d
    @53
    @43
    @18
    @8
    @53
    vf
    vg
    @39
    @39
    @42
    @6
    @6
    @17
    @57
    @57
    @53
    @41
    @16
    @12
    @53
    vh
    @36
    @3
    @15
    @55
    mpteq1d
    opeq2d
    mpt2eq123dv
    opeq2d
    @53
    @46
    @22
    @20
    @53
    @1
    @45
    @21
    @33
    cK
    cedring
    fveq2
    fveq1d
    opeq2d
    tpeq123d
    @53
    @50
    @29
    @53
    @49
    @28
    @25
    @53
    vs
    vf
    @38
    @39
    @27
    @5
    @6
    @27
    @56
    @57
    @53
    @27
    eqidd
    mpt2eq123dv
    opeq2d
    sneqd
    uneq12d
    mpteq12dv
    vw
    vf
    vg
    vh
    vk
    vs
    df-dvech
    vw
    cH
    @31
    cH
    @54
    cvv
    dvhset.h
    cK
    clh
    fvex
    eqeltri
    mptex
    fvmpt
    syl
end

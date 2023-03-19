include "wcel.mm"
include "cvv.mm"
include "cdveca.mm"
include "cfv.mm"
include "cnx.mm"
include "cbs.mm"
include "cv.mm"
include "cltrn.mm"
include "cop.mm"
include "cplusg.mm"
include "ccom.mm"
include "cmpt2.mm"
include "csca.mm"
include "cedring.mm"
include "ctp.mm"
include "cvsca.mm"
include "ctendo.mm"
include "csn.mm"
include "cun.mm"
include "cmpt.mm"
include "wceq.mm"
include "elex.mm"
include "clh.mm"
include "fveq2.mm"
include "syl6eqr.mm"
include "fveq1d.mm"
include "opeq2d.mm"
include "eqidd.mm"
include "mpt2eq123dv.mm"
include "tpeq123d.mm"
include "sneqd.mm"
include "uneq12d.mm"
include "mpteq12dv.mm"
include "df-dveca.mm"
include "fvex.mm"
include "eqeltri.mm"
include "mptex.mm"
include "fvmpt.mm"
include "syl.mm"

theorem dvafset
  let vw: setvar w
  let vf: setvar f
  let vg: setvar g
  let cH: class H
  let cK: class K
  let cV: class V
  let vs: setvar s
  let cD: class D
  let cE: class E
  let vk: setvar k
  let cT: class T
  let cW: class W
  assume dvaset.h: |- H = ( LHyp ` K )

  disjoint H w
  disjoint f g
  disjoint f s
  disjoint f w
  disjoint K f
  disjoint g s
  disjoint g w
  disjoint K g
  disjoint s w
  disjoint K s
  disjoint K w
  disjoint D w
  disjoint E w
  disjoint k w
  disjoint H k
  disjoint f k
  disjoint g k
  disjoint k s
  disjoint K k
  disjoint T w
  disjoint W f
  disjoint W g
  disjoint W k
  disjoint W s
  disjoint W w
  assert |- ( K e. V -> ( DVecA ` K ) = ( w e. H |-> ( { <. ( Base ` ndx ) , ( ( LTrn ` K ) ` w ) >. , <. ( +g ` ndx ) , ( f e. ( ( LTrn ` K ) ` w ) , g e. ( ( LTrn ` K ) ` w ) |-> ( f o. g ) ) >. , <. ( Scalar ` ndx ) , ( ( EDRing ` K ) ` w ) >. } u. { <. ( .s ` ndx ) , ( s e. ( ( TEndo ` K ) ` w ) , f e. ( ( LTrn ` K ) ` w ) |-> ( s ` f ) ) >. } ) ) )

  proof
    cK
    cV
    wcel
    cK
    cvv
    wcel
    cK
    cdveca
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
    cop
    #
    cnx
    cplusg
    cfv
    #
    vf
    vg
    @3
    @3
    vf
    cv
    #
    vg
    cv
    ccom
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
    @1
    cK
    ctendo
    cfv
    #
    cfv
    #
    @3
    @6
    vs
    cv
    cfv
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
    @24
    cltrn
    cfv
    #
    cfv
    #
    cop
    #
    @5
    vf
    vg
    @27
    @27
    @7
    cmpt2
    #
    cop
    #
    @10
    @1
    @24
    cedring
    cfv
    #
    cfv
    #
    cop
    #
    ctp
    #
    @15
    vs
    vf
    @1
    @24
    ctendo
    cfv
    #
    cfv
    #
    @27
    @18
    cmpt2
    #
    cop
    #
    csn
    #
    cun
    #
    cmpt
    @23
    cvv
    cdveca
    @24
    cK
    wceq
    #
    vw
    @25
    @40
    cH
    @22
    @41
    @25
    cK
    clh
    cfv
    #
    cH
    @24
    cK
    clh
    fveq2
    dvaset.h
    syl6eqr
    @41
    @34
    @14
    @39
    @21
    @41
    @28
    @4
    @30
    @9
    @33
    @13
    @41
    @27
    @3
    @0
    @41
    @1
    @26
    @2
    @24
    cK
    cltrn
    fveq2
    fveq1d
    #
    opeq2d
    @41
    @29
    @8
    @5
    @41
    vf
    vg
    @27
    @27
    @7
    @3
    @3
    @7
    @43
    @43
    @41
    @7
    eqidd
    mpt2eq123dv
    opeq2d
    @41
    @32
    @12
    @10
    @41
    @1
    @31
    @11
    @24
    cK
    cedring
    fveq2
    fveq1d
    opeq2d
    tpeq123d
    @41
    @38
    @20
    @41
    @37
    @19
    @15
    @41
    vs
    vf
    @36
    @27
    @18
    @17
    @3
    @18
    @41
    @1
    @35
    @16
    @24
    cK
    ctendo
    fveq2
    fveq1d
    @43
    @41
    @18
    eqidd
    mpt2eq123dv
    opeq2d
    sneqd
    uneq12d
    mpteq12dv
    vw
    vf
    vg
    vk
    vs
    df-dveca
    vw
    cH
    @22
    cH
    @42
    cvv
    dvaset.h
    cK
    clh
    fvex
    eqeltri
    mptex
    fvmpt
    syl
end

include "wcel.mm"
include "cvv.mm"
include "cedring-rN.mm"
include "cfv.mm"
include "cnx.mm"
include "cbs.mm"
include "cv.mm"
include "ctendo.mm"
include "cop.mm"
include "cplusg.mm"
include "cltrn.mm"
include "ccom.mm"
include "cmpt.mm"
include "cmpt2.mm"
include "cmulr.mm"
include "ctp.mm"
include "wceq.mm"
include "elex.mm"
include "clh.mm"
include "fveq2.mm"
include "syl6eqr.mm"
include "fveq1d.mm"
include "opeq2d.mm"
include "mpteq1d.mm"
include "mpt2eq123dv.mm"
include "eqidd.mm"
include "tpeq123d.mm"
include "mpteq12dv.mm"
include "df-edring-rN.mm"
include "fvex.mm"
include "eqeltri.mm"
include "mptex.mm"
include "fvmpt.mm"
include "syl.mm"

theorem erngfset-rN
  let vw: setvar w
  let vt: setvar t
  let vf: setvar f
  let cH: class H
  let cK: class K
  let cV: class V
  let vs: setvar s
  let cE: class E
  let vk: setvar k
  let cT: class T
  assume erngset.h-r: |- H = ( LHyp ` K )

  disjoint H w
  disjoint f s
  disjoint f t
  disjoint f w
  disjoint K f
  disjoint s t
  disjoint s w
  disjoint K s
  disjoint t w
  disjoint K t
  disjoint K w
  disjoint E k
  disjoint k w
  disjoint H k
  disjoint f k
  disjoint k s
  disjoint k t
  disjoint K k
  disjoint T k
  assert |- ( K e. V -> ( EDRingR ` K ) = ( w e. H |-> { <. ( Base ` ndx ) , ( ( TEndo ` K ) ` w ) >. , <. ( +g ` ndx ) , ( s e. ( ( TEndo ` K ) ` w ) , t e. ( ( TEndo ` K ) ` w ) |-> ( f e. ( ( LTrn ` K ) ` w ) |-> ( ( s ` f ) o. ( t ` f ) ) ) ) >. , <. ( .r ` ndx ) , ( s e. ( ( TEndo ` K ) ` w ) , t e. ( ( TEndo ` K ) ` w ) |-> ( t o. s ) ) >. } ) )

  proof
    cK
    cV
    wcel
    cK
    cvv
    wcel
    cK
    cedring-rN
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
    ctendo
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
    vs
    vt
    @3
    @3
    vf
    @1
    cK
    cltrn
    cfv
    #
    cfv
    #
    vf
    cv
    #
    vs
    cv
    #
    cfv
    @8
    vt
    cv
    #
    cfv
    ccom
    #
    cmpt
    #
    cmpt2
    #
    cop
    #
    cnx
    cmulr
    cfv
    #
    vs
    vt
    @3
    @3
    @10
    @9
    ccom
    #
    cmpt2
    #
    cop
    #
    ctp
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
    @21
    ctendo
    cfv
    #
    cfv
    #
    cop
    #
    @5
    vs
    vt
    @24
    @24
    vf
    @1
    @21
    cltrn
    cfv
    #
    cfv
    #
    @11
    cmpt
    #
    cmpt2
    #
    cop
    #
    @15
    vs
    vt
    @24
    @24
    @16
    cmpt2
    #
    cop
    #
    ctp
    #
    cmpt
    @20
    cvv
    cedring-rN
    @21
    cK
    wceq
    #
    vw
    @22
    @33
    cH
    @19
    @34
    @22
    cK
    clh
    cfv
    #
    cH
    @21
    cK
    clh
    fveq2
    erngset.h-r
    syl6eqr
    @34
    @25
    @4
    @30
    @14
    @32
    @18
    @34
    @24
    @3
    @0
    @34
    @1
    @23
    @2
    @21
    cK
    ctendo
    fveq2
    fveq1d
    #
    opeq2d
    @34
    @29
    @13
    @5
    @34
    vs
    vt
    @24
    @24
    @28
    @3
    @3
    @12
    @36
    @36
    @34
    vf
    @27
    @7
    @11
    @34
    @1
    @26
    @6
    @21
    cK
    cltrn
    fveq2
    fveq1d
    mpteq1d
    mpt2eq123dv
    opeq2d
    @34
    @31
    @17
    @15
    @34
    vs
    vt
    @24
    @24
    @16
    @3
    @3
    @16
    @36
    @36
    @34
    @16
    eqidd
    mpt2eq123dv
    opeq2d
    tpeq123d
    mpteq12dv
    vw
    vt
    vf
    vk
    vs
    df-edring-rN
    vw
    cH
    @19
    cH
    @35
    cvv
    erngset.h-r
    cK
    clh
    fvex
    eqeltri
    mptex
    fvmpt
    syl
end

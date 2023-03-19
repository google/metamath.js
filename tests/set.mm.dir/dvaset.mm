include "wcel.mm"
include "wa.mm"
include "cdveca.mm"
include "cfv.mm"
include "cnx.mm"
include "cbs.mm"
include "cop.mm"
include "cplusg.mm"
include "cv.mm"
include "ccom.mm"
include "cmpt2.mm"
include "csca.mm"
include "ctp.mm"
include "cvsca.mm"
include "csn.mm"
include "cun.mm"
include "cltrn.mm"
include "cedring.mm"
include "ctendo.mm"
include "cmpt.mm"
include "dvafset.mm"
include "fveq1d.mm"
include "wceq.mm"
include "fveq2.mm"
include "syl6eqr.mm"
include "opeq2d.mm"
include "eqidd.mm"
include "mpt2eq123dv.mm"
include "tpeq123d.mm"
include "sneqd.mm"
include "uneq12d.mm"
include "eqid.mm"
include "tpex.mm"
include "snex.mm"
include "unex.mm"
include "fvmpt.mm"
include "sylan9eq.mm"
include "syl5eq.mm"

theorem dvaset
  let cD: class D
  let cT: class T
  let cU: class U
  let vf: setvar f
  let vg: setvar g
  let cE: class E
  let cH: class H
  let cK: class K
  let cW: class W
  let cX: class X
  let vs: setvar s
  let vw: setvar w
  let vk: setvar k
  assume dvaset.h: |- H = ( LHyp ` K )
  assume dvaset.t: |- T = ( ( LTrn ` K ) ` W )
  assume dvaset.e: |- E = ( ( TEndo ` K ) ` W )
  assume dvaset.d: |- D = ( ( EDRing ` K ) ` W )
  assume dvaset.u: |- U = ( ( DVecA ` K ) ` W )

  disjoint f g
  disjoint f s
  disjoint K f
  disjoint g s
  disjoint K g
  disjoint K s
  disjoint W f
  disjoint W g
  disjoint W s
  disjoint D w
  disjoint E w
  disjoint k w
  disjoint H k
  disjoint H w
  disjoint f k
  disjoint f w
  disjoint g k
  disjoint g w
  disjoint k s
  disjoint K k
  disjoint s w
  disjoint K w
  disjoint T w
  disjoint W k
  disjoint W w
  assert |- ( ( K e. X /\ W e. H ) -> U = ( { <. ( Base ` ndx ) , T >. , <. ( +g ` ndx ) , ( f e. T , g e. T |-> ( f o. g ) ) >. , <. ( Scalar ` ndx ) , D >. } u. { <. ( .s ` ndx ) , ( s e. E , f e. T |-> ( s ` f ) ) >. } ) )

  proof
    cK
    cX
    wcel
    #
    cW
    cH
    wcel
    #
    wa
    cU
    cW
    cK
    cdveca
    cfv
    #
    cfv
    #
    cnx
    cbs
    cfv
    #
    cT
    cop
    #
    cnx
    cplusg
    cfv
    #
    vf
    vg
    cT
    cT
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
    cD
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
    cE
    cT
    @7
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
    dvaset.u
    @0
    @1
    @3
    cW
    vw
    cH
    @4
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
    @6
    vf
    vg
    @22
    @22
    @8
    cmpt2
    #
    cop
    #
    @11
    @20
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
    @14
    vs
    vf
    @20
    cK
    ctendo
    cfv
    #
    cfv
    #
    @22
    @15
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
    @19
    @0
    cW
    @2
    @36
    vw
    vf
    vg
    cH
    cK
    cX
    vs
    dvaset.h
    dvafset
    fveq1d
    vw
    cW
    @35
    @19
    cH
    @36
    @20
    cW
    wceq
    #
    @29
    @13
    @34
    @18
    @37
    @23
    @5
    @25
    @10
    @28
    @12
    @37
    @22
    cT
    @4
    @37
    @22
    cW
    @21
    cfv
    cT
    @20
    cW
    @21
    fveq2
    dvaset.t
    syl6eqr
    #
    opeq2d
    @37
    @24
    @9
    @6
    @37
    vf
    vg
    @22
    @22
    @8
    cT
    cT
    @8
    @38
    @38
    @37
    @8
    eqidd
    mpt2eq123dv
    opeq2d
    @37
    @27
    cD
    @11
    @37
    @27
    cW
    @26
    cfv
    cD
    @20
    cW
    @26
    fveq2
    dvaset.d
    syl6eqr
    opeq2d
    tpeq123d
    @37
    @33
    @17
    @37
    @32
    @16
    @14
    @37
    vs
    vf
    @31
    @22
    @15
    cE
    cT
    @15
    @37
    @31
    cW
    @30
    cfv
    cE
    @20
    cW
    @30
    fveq2
    dvaset.e
    syl6eqr
    @38
    @37
    @15
    eqidd
    mpt2eq123dv
    opeq2d
    sneqd
    uneq12d
    @36
    eqid
    @13
    @18
    @5
    @10
    @12
    tpex
    @17
    snex
    unex
    fvmpt
    sylan9eq
    syl5eq
end

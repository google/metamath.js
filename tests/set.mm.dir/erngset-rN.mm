include "wcel.mm"
include "cnx.mm"
include "cbs.mm"
include "cfv.mm"
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
include "cedring-rN.mm"
include "erngfset-rN.mm"
include "fveq1d.mm"
include "syl5eq.mm"
include "wceq.mm"
include "fveq2.mm"
include "opeq2d.mm"
include "tpeq1.mm"
include "opeq2i.mm"
include "ax-mp.mm"
include "syl6eqr.mm"
include "syl.mm"
include "eqidd.mm"
include "mpteq12dv.mm"
include "mpt2eq123dv.mm"
include "tpeq2d.mm"
include "tpeq3d.mm"
include "3eqtrd.mm"
include "eqid.mm"
include "tpex.mm"
include "fvmpt.mm"
include "sylan9eq.mm"

theorem erngset-rN
  let vt: setvar t
  let cD: class D
  let cT: class T
  let vf: setvar f
  let cE: class E
  let cH: class H
  let cK: class K
  let cV: class V
  let cW: class W
  let vs: setvar s
  let vk: setvar k
  let vw: setvar w
  assume erngset.h-r: |- H = ( LHyp ` K )
  assume erngset.t-r: |- T = ( ( LTrn ` K ) ` W )
  assume erngset.e-r: |- E = ( ( TEndo ` K ) ` W )
  assume erngset.d-r: |- D = ( ( EDRingR ` K ) ` W )

  disjoint f s
  disjoint f t
  disjoint K f
  disjoint s t
  disjoint K s
  disjoint K t
  disjoint W f
  disjoint W s
  disjoint W t
  disjoint E k
  disjoint k w
  disjoint H k
  disjoint H w
  disjoint f k
  disjoint f w
  disjoint k s
  disjoint k t
  disjoint K k
  disjoint s w
  disjoint t w
  disjoint K w
  disjoint T k
  disjoint E w
  disjoint T w
  disjoint W w
  assert |- ( ( K e. V /\ W e. H ) -> D = { <. ( Base ` ndx ) , E >. , <. ( +g ` ndx ) , ( s e. E , t e. E |-> ( f e. T |-> ( ( s ` f ) o. ( t ` f ) ) ) ) >. , <. ( .r ` ndx ) , ( s e. E , t e. E |-> ( t o. s ) ) >. } )

  proof
    cK
    cV
    wcel
    #
    cW
    cH
    wcel
    cD
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
    @4
    @4
    vf
    @2
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
    @9
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
    @4
    @4
    @11
    @10
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
    cfv
    #
    @1
    cE
    cop
    #
    @6
    vs
    vt
    cE
    cE
    vf
    cT
    @12
    cmpt
    #
    cmpt2
    #
    cop
    #
    @16
    vs
    vt
    cE
    cE
    @17
    cmpt2
    #
    cop
    #
    ctp
    #
    @0
    cD
    cW
    cK
    cedring-rN
    cfv
    #
    cfv
    @22
    erngset.d-r
    @0
    cW
    @30
    @21
    vw
    vt
    vf
    cH
    cK
    cV
    vs
    erngset.h-r
    erngfset-rN
    fveq1d
    syl5eq
    vw
    cW
    @20
    @29
    cH
    @21
    @2
    cW
    wceq
    #
    @20
    @23
    @15
    @19
    ctp
    #
    @23
    @26
    @19
    ctp
    @29
    @31
    @5
    @1
    cW
    @3
    cfv
    #
    cop
    #
    wceq
    #
    @20
    @32
    wceq
    @31
    @4
    @33
    @1
    @2
    cW
    @3
    fveq2
    #
    opeq2d
    @35
    @20
    @34
    @15
    @19
    ctp
    #
    @32
    @5
    @34
    @15
    @19
    tpeq1
    @23
    @34
    wceq
    @32
    @37
    wceq
    cE
    @33
    @1
    erngset.e-r
    opeq2i
    @23
    @34
    @15
    @19
    tpeq1
    ax-mp
    syl6eqr
    syl
    @31
    @15
    @26
    @23
    @19
    @31
    @14
    @25
    @6
    @31
    vs
    vt
    @4
    @4
    @13
    cE
    cE
    @24
    @31
    @4
    @33
    cE
    @36
    erngset.e-r
    syl6eqr
    #
    @38
    @31
    vf
    @8
    @12
    cT
    @12
    @31
    @8
    cW
    @7
    cfv
    cT
    @2
    cW
    @7
    fveq2
    erngset.t-r
    syl6eqr
    @31
    @12
    eqidd
    mpteq12dv
    mpt2eq123dv
    opeq2d
    tpeq2d
    @31
    @19
    @28
    @23
    @26
    @31
    @18
    @27
    @16
    @31
    vs
    vt
    @4
    @4
    @17
    cE
    cE
    @17
    @38
    @38
    @31
    @17
    eqidd
    mpt2eq123dv
    opeq2d
    tpeq3d
    3eqtrd
    @21
    eqid
    @23
    @26
    @28
    tpex
    fvmpt
    sylan9eq
end

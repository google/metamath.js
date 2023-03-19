include "cngp.mm"
include "wcel.mm"
include "wa.mm"
include "cnmo.mm"
include "co.mm"
include "cghm.mm"
include "cv.mm"
include "cfv.mm"
include "cmul.mm"
include "cle.mm"
include "wbr.mm"
include "wral.mm"
include "cc0.mm"
include "cpnf.mm"
include "cico.mm"
include "crab.mm"
include "cxr.mm"
include "clt.mm"
include "cinf.mm"
include "cmpt.mm"
include "cnm.mm"
include "cbs.mm"
include "wceq.mm"
include "oveq12.mm"
include "simpl.mm"
include "fveq2d.mm"
include "syl6eqr.mm"
include "simpr.mm"
include "fveq1d.mm"
include "oveq2d.mm"
include "breq12d.mm"
include "raleqbidv.mm"
include "rabbidv.mm"
include "infeq1d.mm"
include "mpteq12dv.mm"
include "df-nmo.mm"
include "wf.mm"
include "cvv.mm"
include "eqid.mm"
include "wss.mm"
include "ssrab2.mm"
include "icossxr.mm"
include "sstri.mm"
include "infxrcl.mm"
include "mp1i.mm"
include "fmpti.mm"
include "ovex.mm"
include "xrex.mm"
include "fex2.mm"
include "mp3an.mm"
include "ovmpt2a.mm"
include "syl5eq.mm"

theorem nmofval
  let vx: setvar x
  let cS: class S
  let cT: class T
  let vf: setvar f
  let cL: class L
  let cM: class M
  let cN: class N
  let cV: class V
  let vr: setvar r
  let vs: setvar s
  let vt: setvar t
  let cA: class A
  let cF: class F
  let wph: wff ph
  let cX: class X
  assume nmofval.1: |- N = ( S normOp T )
  assume nmofval.2: |- V = ( Base ` S )
  assume nmofval.3: |- L = ( norm ` S )
  assume nmofval.4: |- M = ( norm ` T )

  disjoint f r
  disjoint f x
  disjoint L f
  disjoint r x
  disjoint L r
  disjoint L x
  disjoint M f
  disjoint M r
  disjoint M x
  disjoint S f
  disjoint S r
  disjoint S x
  disjoint T f
  disjoint T r
  disjoint T x
  disjoint V f
  disjoint V r
  disjoint V x
  disjoint N r
  disjoint N x
  disjoint f s
  disjoint f t
  disjoint r s
  disjoint r t
  disjoint s t
  disjoint s x
  disjoint L s
  disjoint t x
  disjoint L t
  disjoint M s
  disjoint M t
  disjoint S s
  disjoint S t
  disjoint T s
  disjoint T t
  disjoint A r
  disjoint A s
  disjoint A x
  disjoint F f
  disjoint F r
  disjoint F s
  disjoint F x
  disjoint ph x
  disjoint V s
  disjoint V t
  disjoint X r
  disjoint X x
  disjoint N s
  disjoint N t
  assert |- ( ( S e. NrmGrp /\ T e. NrmGrp ) -> N = ( f e. ( S GrpHom T ) |-> inf ( { r e. ( 0 [,) +oo ) | A. x e. V ( M ` ( f ` x ) ) <_ ( r x. ( L ` x ) ) } , RR* , < ) ) )

  proof
    cS
    cngp
    wcel
    cT
    cngp
    wcel
    wa
    cN
    cS
    cT
    cnmo
    co
    vf
    cS
    cT
    cghm
    co
    #
    vx
    cv
    #
    vf
    cv
    #
    cfv
    #
    cM
    cfv
    #
    vr
    cv
    #
    @1
    cL
    cfv
    #
    cmul
    co
    #
    cle
    wbr
    #
    vx
    cV
    wral
    #
    vr
    cc0
    cpnf
    cico
    co
    #
    crab
    #
    cxr
    clt
    cinf
    #
    cmpt
    #
    nmofval.1
    vs
    vt
    cS
    cT
    cngp
    cngp
    vf
    vs
    cv
    #
    vt
    cv
    #
    cghm
    co
    #
    @3
    @15
    cnm
    cfv
    #
    cfv
    #
    @5
    @1
    @14
    cnm
    cfv
    #
    cfv
    #
    cmul
    co
    #
    cle
    wbr
    #
    vx
    @14
    cbs
    cfv
    #
    wral
    #
    vr
    @10
    crab
    #
    cxr
    clt
    cinf
    #
    cmpt
    @13
    cnmo
    @14
    cS
    wceq
    #
    @15
    cT
    wceq
    #
    wa
    #
    vf
    @16
    @26
    @0
    @12
    @14
    cS
    @15
    cT
    cghm
    oveq12
    @29
    cxr
    @25
    @11
    clt
    @29
    @24
    @9
    vr
    @10
    @29
    @22
    @8
    vx
    @23
    cV
    @29
    @23
    cS
    cbs
    cfv
    cV
    @29
    @14
    cS
    cbs
    @27
    @28
    simpl
    #
    fveq2d
    nmofval.2
    syl6eqr
    @29
    @18
    @4
    @21
    @7
    cle
    @29
    @3
    @17
    cM
    @29
    @17
    cT
    cnm
    cfv
    cM
    @29
    @15
    cT
    cnm
    @27
    @28
    simpr
    fveq2d
    nmofval.4
    syl6eqr
    fveq1d
    @29
    @20
    @6
    @5
    cmul
    @29
    @1
    @19
    cL
    @29
    @19
    cS
    cnm
    cfv
    cL
    @29
    @14
    cS
    cnm
    @30
    fveq2d
    nmofval.3
    syl6eqr
    fveq1d
    oveq2d
    breq12d
    raleqbidv
    rabbidv
    infeq1d
    mpteq12dv
    vx
    vt
    vf
    vs
    vr
    df-nmo
    @0
    cxr
    @13
    wf
    @0
    cvv
    wcel
    cxr
    cvv
    wcel
    @13
    cvv
    wcel
    vf
    @0
    cxr
    @12
    @13
    @13
    eqid
    @11
    cxr
    wss
    @12
    cxr
    wcel
    @2
    @0
    wcel
    @11
    @10
    cxr
    @9
    vr
    @10
    ssrab2
    cc0
    cpnf
    icossxr
    sstri
    @11
    infxrcl
    mp1i
    fmpti
    cS
    cT
    cghm
    ovex
    xrex
    @0
    cxr
    @13
    cvv
    cvv
    fex2
    mp3an
    ovmpt2a
    syl5eq
end

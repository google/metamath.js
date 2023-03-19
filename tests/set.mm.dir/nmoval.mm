include "cngp.mm"
include "wcel.mm"
include "cghm.mm"
include "co.mm"
include "cfv.mm"
include "cv.mm"
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
include "wceq.mm"
include "wa.mm"
include "cmpt.mm"
include "nmofval.mm"
include "fveq1d.mm"
include "fveq1.mm"
include "fveq2d.mm"
include "breq1d.mm"
include "ralbidv.mm"
include "rabbidv.mm"
include "infeq1d.mm"
include "eqid.mm"
include "xrltso.mm"
include "infex.mm"
include "fvmpt.mm"
include "sylan9eq.mm"
include "3impa.mm"

theorem nmoval
  let vx: setvar x
  let cS: class S
  let cT: class T
  let cF: class F
  let cL: class L
  let cM: class M
  let cN: class N
  let cV: class V
  let vr: setvar r
  let vf: setvar f
  let vs: setvar s
  let vt: setvar t
  let cA: class A
  let wph: wff ph
  let cX: class X
  assume nmofval.1: |- N = ( S normOp T )
  assume nmofval.2: |- V = ( Base ` S )
  assume nmofval.3: |- L = ( norm ` S )
  assume nmofval.4: |- M = ( norm ` T )

  disjoint r x
  disjoint L r
  disjoint L x
  disjoint M r
  disjoint M x
  disjoint S r
  disjoint S x
  disjoint T r
  disjoint T x
  disjoint F r
  disjoint F x
  disjoint V r
  disjoint V x
  disjoint N r
  disjoint N x
  disjoint f r
  disjoint f s
  disjoint f t
  disjoint f x
  disjoint L f
  disjoint r s
  disjoint r t
  disjoint s t
  disjoint s x
  disjoint L s
  disjoint t x
  disjoint L t
  disjoint M f
  disjoint M s
  disjoint M t
  disjoint S f
  disjoint S s
  disjoint S t
  disjoint T f
  disjoint T s
  disjoint T t
  disjoint A r
  disjoint A s
  disjoint A x
  disjoint F f
  disjoint F s
  disjoint ph x
  disjoint V f
  disjoint V s
  disjoint V t
  disjoint X r
  disjoint X x
  disjoint N s
  disjoint N t
  assert |- ( ( S e. NrmGrp /\ T e. NrmGrp /\ F e. ( S GrpHom T ) ) -> ( N ` F ) = inf ( { r e. ( 0 [,) +oo ) | A. x e. V ( M ` ( F ` x ) ) <_ ( r x. ( L ` x ) ) } , RR* , < ) )

  proof
    cS
    cngp
    wcel
    #
    cT
    cngp
    wcel
    #
    cF
    cS
    cT
    cghm
    co
    #
    wcel
    #
    cF
    cN
    cfv
    #
    vx
    cv
    #
    cF
    cfv
    #
    cM
    cfv
    #
    vr
    cv
    @5
    cL
    cfv
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
    wceq
    @0
    @1
    wa
    #
    @3
    @4
    cF
    vf
    @2
    @5
    vf
    cv
    #
    cfv
    #
    cM
    cfv
    #
    @8
    cle
    wbr
    #
    vx
    cV
    wral
    #
    vr
    @11
    crab
    #
    cxr
    clt
    cinf
    #
    cmpt
    #
    cfv
    @13
    @14
    cF
    cN
    @22
    vx
    cS
    cT
    vf
    cL
    cM
    cN
    cV
    vr
    nmofval.1
    nmofval.2
    nmofval.3
    nmofval.4
    nmofval
    fveq1d
    vf
    cF
    @21
    @13
    @2
    @22
    @15
    cF
    wceq
    #
    cxr
    @20
    @12
    clt
    @23
    @19
    @10
    vr
    @11
    @23
    @18
    @9
    vx
    cV
    @23
    @17
    @7
    @8
    cle
    @23
    @16
    @6
    cM
    @5
    @15
    cF
    fveq1
    fveq2d
    breq1d
    ralbidv
    rabbidv
    infeq1d
    @22
    eqid
    cxr
    @12
    clt
    xrltso
    infex
    fvmpt
    sylan9eq
    3impa
end

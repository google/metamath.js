include "cngp.mm"
include "wcel.mm"
include "cghm.mm"
include "co.mm"
include "w3a.mm"
include "cfv.mm"
include "cle.mm"
include "wbr.mm"
include "cv.mm"
include "cmul.mm"
include "wral.mm"
include "cc0.mm"
include "cpnf.mm"
include "cico.mm"
include "crab.mm"
include "cxr.mm"
include "clt.mm"
include "cinf.mm"
include "wi.mm"
include "nmoval.mm"
include "breq2d.mm"
include "wss.mm"
include "wb.mm"
include "ssrab2.mm"
include "icossxr.mm"
include "sstri.mm"
include "infxrgelb.mm"
include "mpan.mm"
include "breq2.mm"
include "ralrab2.mm"
include "syl6bb.mm"
include "sylan9bb.mm"

theorem nmogelb
  let vx: setvar x
  let cA: class A
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
  disjoint A r
  disjoint A x
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
  disjoint A s
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
  assert |- ( ( ( S e. NrmGrp /\ T e. NrmGrp /\ F e. ( S GrpHom T ) ) /\ A e. RR* ) -> ( A <_ ( N ` F ) <-> A. r e. ( 0 [,) +oo ) ( A. x e. V ( M ` ( F ` x ) ) <_ ( r x. ( L ` x ) ) -> A <_ r ) ) )

  proof
    cS
    cngp
    wcel
    cT
    cngp
    wcel
    cF
    cS
    cT
    cghm
    co
    wcel
    w3a
    #
    cA
    cF
    cN
    cfv
    #
    cle
    wbr
    cA
    vx
    cv
    #
    cF
    cfv
    cM
    cfv
    vr
    cv
    #
    @2
    cL
    cfv
    cmul
    co
    cle
    wbr
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
    cle
    wbr
    #
    cA
    cxr
    wcel
    #
    @4
    cA
    @3
    cle
    wbr
    #
    wi
    vr
    @5
    wral
    #
    @0
    @1
    @7
    cA
    cle
    vx
    cS
    cT
    cF
    cL
    cM
    cN
    cV
    vr
    nmofval.1
    nmofval.2
    nmofval.3
    nmofval.4
    nmoval
    breq2d
    @9
    @8
    cA
    vs
    cv
    #
    cle
    wbr
    #
    vs
    @6
    wral
    #
    @11
    @6
    cxr
    wss
    @9
    @8
    @14
    wb
    @6
    @5
    cxr
    @4
    vr
    @5
    ssrab2
    cc0
    cpnf
    icossxr
    sstri
    vs
    @6
    cA
    infxrgelb
    mpan
    @4
    @13
    @10
    vs
    vr
    @5
    @12
    @3
    cA
    cle
    breq2
    ralrab2
    syl6bb
    sylan9bb
end

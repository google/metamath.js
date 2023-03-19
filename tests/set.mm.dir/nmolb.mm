include "cngp.mm"
include "wcel.mm"
include "cghm.mm"
include "co.mm"
include "w3a.mm"
include "cr.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "cv.mm"
include "cfv.mm"
include "cmul.mm"
include "wral.mm"
include "wi.mm"
include "wa.mm"
include "cpnf.mm"
include "cico.mm"
include "elrege0.mm"
include "cxr.mm"
include "crab.mm"
include "clt.mm"
include "cinf.mm"
include "nmoval.mm"
include "wss.mm"
include "ssrab2.mm"
include "icossxr.mm"
include "sstri.mm"
include "infxrcl.mm"
include "mp1i.mm"
include "eqeltrd.mm"
include "xrleid.mm"
include "syl.mm"
include "wb.mm"
include "nmogelb.mm"
include "mpdan.mm"
include "mpbid.mm"
include "wceq.mm"
include "oveq1.mm"
include "breq2d.mm"
include "ralbidv.mm"
include "breq2.mm"
include "imbi12d.mm"
include "rspccv.mm"
include "syl5bir.mm"
include "3impib.mm"

theorem nmolb
  let vx: setvar x
  let cA: class A
  let cS: class S
  let cT: class T
  let cF: class F
  let cL: class L
  let cM: class M
  let cN: class N
  let cV: class V
  let vf: setvar f
  let vr: setvar r
  let vs: setvar s
  let vt: setvar t
  let wph: wff ph
  let cX: class X
  assume nmofval.1: |- N = ( S normOp T )
  assume nmofval.2: |- V = ( Base ` S )
  assume nmofval.3: |- L = ( norm ` S )
  assume nmofval.4: |- M = ( norm ` T )

  disjoint L x
  disjoint M x
  disjoint S x
  disjoint T x
  disjoint A x
  disjoint F x
  disjoint V x
  disjoint N x
  disjoint f r
  disjoint f s
  disjoint f t
  disjoint f x
  disjoint L f
  disjoint r s
  disjoint r t
  disjoint r x
  disjoint L r
  disjoint s t
  disjoint s x
  disjoint L s
  disjoint t x
  disjoint L t
  disjoint M f
  disjoint M r
  disjoint M s
  disjoint M t
  disjoint S f
  disjoint S r
  disjoint S s
  disjoint S t
  disjoint T f
  disjoint T r
  disjoint T s
  disjoint T t
  disjoint A r
  disjoint A s
  disjoint F f
  disjoint F r
  disjoint F s
  disjoint ph x
  disjoint V f
  disjoint V r
  disjoint V s
  disjoint V t
  disjoint X r
  disjoint X x
  disjoint N r
  disjoint N s
  disjoint N t
  assert |- ( ( ( S e. NrmGrp /\ T e. NrmGrp /\ F e. ( S GrpHom T ) ) /\ A e. RR /\ 0 <_ A ) -> ( A. x e. V ( M ` ( F ` x ) ) <_ ( A x. ( L ` x ) ) -> ( N ` F ) <_ A ) )

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
    cr
    wcel
    #
    cc0
    cA
    cle
    wbr
    #
    vx
    cv
    #
    cF
    cfv
    cM
    cfv
    #
    cA
    @3
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
    cF
    cN
    cfv
    #
    cA
    cle
    wbr
    #
    wi
    #
    @1
    @2
    wa
    cA
    cc0
    cpnf
    cico
    co
    #
    wcel
    #
    @0
    @11
    cA
    elrege0
    @0
    @4
    vr
    cv
    #
    @5
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
    @9
    @14
    cle
    wbr
    #
    wi
    #
    vr
    @12
    wral
    #
    @13
    @11
    wi
    @0
    @9
    @9
    cle
    wbr
    #
    @20
    @0
    @9
    cxr
    wcel
    #
    @21
    @0
    @9
    @17
    vr
    @12
    crab
    #
    cxr
    clt
    cinf
    #
    cxr
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
    @23
    cxr
    wss
    @24
    cxr
    wcel
    @0
    @23
    @12
    cxr
    @17
    vr
    @12
    ssrab2
    cc0
    cpnf
    icossxr
    sstri
    @23
    infxrcl
    mp1i
    eqeltrd
    #
    @9
    xrleid
    syl
    @0
    @22
    @21
    @20
    wb
    @25
    vx
    @9
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
    nmogelb
    mpdan
    mpbid
    @19
    @11
    vr
    cA
    @12
    @14
    cA
    wceq
    #
    @17
    @8
    @18
    @10
    @26
    @16
    @7
    vx
    cV
    @26
    @15
    @6
    @4
    cle
    @14
    cA
    @5
    cmul
    oveq1
    breq2d
    ralbidv
    @14
    cA
    @9
    cle
    breq2
    imbi12d
    rspccv
    syl
    syl5bir
    3impib
end
